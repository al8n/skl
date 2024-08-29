use core::{mem, ptr::NonNull};
use std::boxed::Box;

use either::Either;
use options::CompressionPolicy;
use rarena_allocator::Allocator as _;

use super::{allocator::*, common::*, *};

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
use error::{bad_magic_version, bad_version, invalid_data};

mod api;

mod entry;
pub use entry::*;

mod iterator;
pub use iterator::*;

type UpdateOk<'a, 'b, A> = Either<
  Option<VersionedEntryRef<'a, A>>,
  Result<VersionedEntryRef<'a, A>, VersionedEntryRef<'a, A>>,
>;

/// A fast, cocnurrent map implementation based on skiplist that supports forward
/// and backward iteration.
#[derive(Debug)]
pub struct SkipList<A: Allocator, C = Ascend> {
  pub(crate) arena: A,
  meta: NonNull<A::Header>,
  head: <A::Node as Node>::Pointer,
  tail: <A::Node as Node>::Pointer,
  data_offset: u32,
  on_disk: bool,
  opts: Options,
  /// If set to true by tests, then extra delays are added to make it easier to
  /// detect unusual race conditions.
  #[cfg(all(test, feature = "std"))]
  yield_now: bool,

  cmp: C,
}

unsafe impl<A, C> Send for SkipList<A, C>
where
  A: Allocator + Send,
  C: Comparator + Send,
{
}
unsafe impl<A, C> Sync for SkipList<A, C>
where
  A: Allocator + Sync,
  C: Comparator + Sync,
{
}

impl<A, C: Clone> Clone for SkipList<A, C>
where
  A: Allocator,
  C: Clone,
{
  fn clone(&self) -> Self {
    Self {
      arena: self.arena.clone(),
      meta: self.meta,
      on_disk: self.on_disk,
      head: self.head,
      tail: self.tail,
      data_offset: self.data_offset,
      opts: self.opts,
      #[cfg(all(test, feature = "std"))]
      yield_now: self.yield_now,
      cmp: self.cmp.clone(),
    }
  }
}

impl<A, C> Drop for SkipList<A, C>
where
  A: Allocator,
{
  fn drop(&mut self) {
    if self.arena.refs() == 1 {
      if !self.opts.unify() {
        unsafe {
          let _ = Box::from_raw(self.meta.as_ptr());
        }
      }

      #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(windows)))]
      if self.arena.is_mmap() {
        let _ = unsafe { self.arena.munlock(0, self.arena.page_size()) };
      }
    }
  }
}

impl<A, C> SkipList<A, C>
where
  A: Allocator,
{
  fn new_in(arena: A, cmp: C, opts: Options) -> Result<Self, Error> {
    let data_offset = Self::check_capacity(&arena, opts.max_height().into())?;
    if arena.read_only() {
      let (meta, head, tail) = Self::get_pointers(&arena);

      return Ok(Self::construct(
        arena,
        meta,
        head,
        tail,
        data_offset,
        opts,
        cmp,
      ));
    }

    let meta = if opts.unify() {
      arena.allocate_header(opts.magic_version())?
    } else {
      unsafe {
        NonNull::new_unchecked(Box::into_raw(Box::new(<A::Header as Header>::new(
          opts.magic_version(),
        ))))
      }
    };

    let max_height: u8 = opts.max_height().into();
    let head = arena.allocate_full_node(max_height)?;
    let tail = arena.allocate_full_node(max_height)?;

    // Safety:
    // We will always allocate enough space for the head node and the tail node.
    unsafe {
      // Link all head/tail levels together.
      for i in 0..(max_height as usize) {
        let head_link = head.tower::<A>(&arena, i);
        let tail_link = tail.tower::<A>(&arena, i);
        head_link.store_next_offset(tail.offset(), Ordering::Relaxed);
        tail_link.store_prev_offset(head.offset(), Ordering::Relaxed);
      }
    }

    Ok(Self::construct(
      arena,
      meta,
      head,
      tail,
      data_offset,
      opts,
      cmp,
    ))
  }

  /// Checks if the arena has enough capacity to store the skiplist,
  /// and returns the data offset.
  #[inline]
  fn check_capacity(arena: &A, max_height: u8) -> Result<u32, Error> {
    let offset = arena.data_offset();

    let alignment = mem::align_of::<A::Header>();
    let meta_offset = (offset + alignment - 1) & !(alignment - 1);
    let meta_end = meta_offset + mem::size_of::<A::Header>();

    let alignment = mem::align_of::<A::Node>();
    let head_offset = (meta_end + alignment - 1) & !(alignment - 1);
    let head_end = head_offset
      + mem::size_of::<A::Node>()
      + mem::size_of::<<A::Node as Node>::Link>() * max_height as usize;

    let trailer_alignment = mem::align_of::<A::Trailer>();
    let trailer_size = mem::size_of::<A::Trailer>();
    let trailer_end = if trailer_size != 0 {
      let trailer_offset = (head_end + trailer_alignment - 1) & !(trailer_alignment - 1);
      trailer_offset + trailer_size
    } else {
      head_end
    };

    let tail_offset = (trailer_end + alignment - 1) & !(alignment - 1);
    let tail_end = tail_offset
      + mem::size_of::<A::Node>()
      + mem::size_of::<<A::Node as Node>::Link>() * max_height as usize;
    let trailer_end = if trailer_size != 0 {
      let trailer_offset = (tail_end + trailer_alignment - 1) & !(trailer_alignment - 1);
      trailer_offset + trailer_size
    } else {
      tail_end
    };
    if trailer_end > arena.capacity() {
      return Err(Error::ArenaTooSmall);
    }

    Ok(trailer_end as u32)
  }

  #[inline]
  fn get_pointers(
    arena: &A,
  ) -> (
    NonNull<A::Header>,
    <A::Node as Node>::Pointer,
    <A::Node as Node>::Pointer,
  ) {
    unsafe {
      let offset = arena.data_offset();
      let meta = arena.get_aligned_pointer::<A::Header>(offset);

      let offset = arena.offset(meta as _) + mem::size_of::<A::Header>();
      let head_ptr = arena.get_aligned_pointer::<A::Node>(offset);
      let head_offset = arena.offset(head_ptr as _);
      let head =
        <<A::Node as Node>::Pointer as NodePointer>::new(head_ptr as _, head_offset as u32);

      let (trailer_offset, _) = head.as_ref().value_pointer().load();
      let offset = trailer_offset as usize + mem::size_of::<A::Trailer>();
      let tail_ptr = arena.get_aligned_pointer::<A::Node>(offset);
      let tail_offset = arena.offset(tail_ptr as _);
      let tail =
        <<A::Node as Node>::Pointer as NodePointer>::new(tail_ptr as _, tail_offset as u32);
      (NonNull::new_unchecked(meta as _), head, tail)
    }
  }

  #[inline]
  fn construct(
    arena: A,
    meta: NonNull<A::Header>,
    head: <A::Node as Node>::Pointer,
    tail: <A::Node as Node>::Pointer,
    data_offset: u32,
    opts: Options,
    cmp: C,
  ) -> Self {
    Self {
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      on_disk: arena.is_ondisk(),
      arena,
      meta,
      head,
      tail,
      data_offset,
      opts,
      #[cfg(all(test, feature = "std"))]
      yield_now: false,
      cmp,
    }
  }

  #[inline]
  const fn meta(&self) -> &A::Header {
    // Safety: the pointer is well aligned and initialized.
    unsafe { self.meta.as_ref() }
  }
}

impl<A, C> SkipList<A, C>
where
  A: Allocator,
{
  fn new_node<'a, 'b: 'a, E>(
    &'a self,
    version: Version,
    height: u32,
    key: &Key<'a, 'b, A>,
    value_builder: Option<ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>>,
    trailer: A::Trailer,
  ) -> Result<(<A::Node as Node>::Pointer, Deallocator), Either<E, Error>> {
    let (nd, deallocator) = match key {
      Key::Occupied(key) => {
        let kb = KeyBuilder::new(KeySize::from_u32_unchecked(key.len() as u32), |buf| {
          buf.write(key).expect("buffer must be large enough for key");
          Ok(())
        });
        let vb = value_builder.unwrap();
        self
          .arena
          .allocate_entry_node::<E>(version, height, trailer, kb, vb)?
      }
      Key::Vacant(key) => self.arena.allocate_value_node::<E>(
        version,
        height,
        trailer,
        key.len() as u32,
        key.offset,
        value_builder.unwrap(),
      )?,
      Key::Pointer { offset, len, .. } => self.arena.allocate_value_node::<E>(
        version,
        height,
        trailer,
        *len,
        *offset,
        value_builder.unwrap(),
      )?,
      Key::Remove(key) => self.arena.allocate_key_node::<E>(
        version,
        height,
        trailer,
        key.len() as u32,
        |buf| {
          buf.write(key).expect("buffer must be large enough for key");
          Ok(())
        },
        <A::Node as Node>::ValuePointer::REMOVE,
      )?,
      Key::RemoveVacant(key) => self.arena.allocate_node_in::<E>(
        version,
        height,
        trailer,
        key.offset,
        key.len() as u32,
        <A::Node as Node>::ValuePointer::REMOVE,
      )?,
      Key::RemovePointer { offset, len, .. } => self.arena.allocate_node_in::<E>(
        version,
        height,
        trailer,
        *offset,
        *len,
        <A::Node as Node>::ValuePointer::REMOVE,
      )?,
    };

    // Try to increase self.height via CAS.
    let meta = self.meta();
    let mut list_height = meta.height();
    while height as u8 > list_height {
      match meta.compare_exchange_height_weak(
        list_height,
        height as u8,
        Ordering::SeqCst,
        Ordering::Acquire,
      ) {
        // Successfully increased skiplist.height.
        Ok(_) => break,
        Err(h) => list_height = h,
      }
    }
    Ok((nd, deallocator))
  }
}

impl<A, C> SkipList<A, C>
where
  A: Allocator,
  C: Comparator,
{
  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[inline]
  unsafe fn get_prev(
    &self,
    mut nd: <A::Node as Node>::Pointer,
    height: usize,
    ignore_invalid_trailer: bool,
  ) -> <A::Node as Node>::Pointer {
    loop {
      if nd.is_null() {
        return <A::Node as Node>::Pointer::NULL;
      }

      if nd.ptr() == self.head.ptr() {
        return self.head;
      }

      let offset = nd.prev_offset(&self.arena, height);
      let ptr = self.arena.get_pointer(offset as usize);
      let prev = <A::Node as Node>::Pointer::new(ptr as _, offset);
      let prev_node = prev.as_ref();

      if ignore_invalid_trailer && !prev_node.get_trailer(&self.arena).is_valid() {
        nd = prev;
        continue;
      }

      return prev;
    }
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[inline]
  unsafe fn get_next(
    &self,
    mut nptr: <A::Node as Node>::Pointer,
    height: usize,
    ignore_invalid_trailer: bool,
  ) -> <A::Node as Node>::Pointer {
    loop {
      if nptr.is_null() {
        return <A::Node as Node>::Pointer::NULL;
      }

      if nptr.ptr() == self.tail.ptr() {
        return self.tail;
      }

      let offset = nptr.next_offset(&self.arena, height);
      let ptr = self.arena.get_pointer(offset as usize);

      let next = <A::Node as Node>::Pointer::new(ptr as _, offset);
      let next_node = next.as_ref();

      if ignore_invalid_trailer && !next_node.get_trailer(&self.arena).is_valid() {
        nptr = next;
        continue;
      }

      return next;
    }
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[inline]
  unsafe fn get_next_allow_uncommitted(
    &self,
    nptr: <A::Node as Node>::Pointer,
    height: usize,
  ) -> <A::Node as Node>::Pointer {
    if nptr.is_null() {
      return <A::Node as Node>::Pointer::NULL;
    }

    let offset = nptr.next_offset(&self.arena, height);
    let ptr = self.arena.get_pointer(offset as usize);

    <A::Node as Node>::Pointer::new(ptr as _, offset)
  }

  /// Returns the first entry in the map.
  fn first_in(
    &self,
    version: Version,
    ignore_invalid_trailer: bool,
  ) -> Option<<A::Node as Node>::Pointer> {
    // Safety: head node was definitely allocated by self.arena
    let nd = unsafe { self.get_next(self.head, 0, ignore_invalid_trailer) };

    if nd.is_null() || nd.ptr() == self.tail.ptr() {
      return None;
    }

    unsafe {
      let node = nd.as_ref();
      let curr_key = node.get_key(&self.arena);
      self.ge(version, curr_key, ignore_invalid_trailer)
    }
  }

  /// Returns the last entry in the map.
  fn last_in(
    &self,
    version: Version,
    ignore_invalid_trailer: bool,
  ) -> Option<<A::Node as Node>::Pointer> {
    // Safety: tail node was definitely allocated by self.arena
    let nd = unsafe { self.get_prev(self.tail, 0, ignore_invalid_trailer) };

    if nd.is_null() || nd.ptr() == self.head.ptr() {
      return None;
    }

    unsafe {
      let node = nd.as_ref();
      let curr_key = node.get_key(&self.arena);
      self.le(version, curr_key, ignore_invalid_trailer)
    }
  }

  /// Returns the entry greater or equal to the given key, if it exists.
  ///
  /// e.g.
  ///
  /// - If k1 < k2 < k3, key is equal to k1, then the entry contains k2 will be returned.
  /// - If k1 < k2 < k3, and k1 < key < k2, then the entry contains k2 will be returned.
  pub(crate) fn gt<'a, 'b: 'a>(
    &'a self,
    version: Version,
    key: &'b [u8],
    ignore_invalid_trailer: bool,
  ) -> Option<<A::Node as Node>::Pointer> {
    unsafe {
      let (n, _) = self.find_near(Version::MIN, key, false, false, ignore_invalid_trailer); // find the key with the max version.

      let n = n?;

      if n.is_null() || n.ptr() == self.tail.ptr() {
        return None;
      }

      self.find_next_max_version(n, version, ignore_invalid_trailer)
    }
  }

  /// Returns the entry less than the given key, if it exists.
  ///
  /// e.g.
  ///
  /// - If k1 < k2 < k3, and key is equal to k3, then the entry contains k2 will be returned.
  /// - If k1 < k2 < k3, and k2 < key < k3, then the entry contains k2 will be returned.
  pub(crate) fn lt<'a, 'b: 'a>(
    &'a self,
    version: Version,
    key: &'b [u8],
    ignore_invalid_trailer: bool,
  ) -> Option<<A::Node as Node>::Pointer> {
    unsafe {
      let (n, _) = self.find_near(Version::MAX, key, true, false, ignore_invalid_trailer); // find less or equal.

      let n = n?;
      if n.is_null() || n.ptr() == self.head.ptr() {
        return None;
      }

      self.find_prev_max_version(n, version, ignore_invalid_trailer)
    }
  }

  /// Returns the entry greater than or equal to the given key, if it exists.
  ///
  /// e.g.
  ///
  /// - If k1 < k2 < k3, key is equal to k1, then the entry contains k1 will be returned.
  /// - If k1 < k2 < k3, and k1 < key < k2, then the entry contains k2 will be returned.
  pub(crate) fn ge<'a, 'b: 'a>(
    &'a self,
    version: Version,
    key: &'b [u8],
    ignore_invalid_trailer: bool,
  ) -> Option<<A::Node as Node>::Pointer> {
    unsafe {
      let (n, _) = self.find_near(Version::MAX, key, false, true, ignore_invalid_trailer); // find the key with the max version.

      let n = n?;

      if n.is_null() || n.ptr() == self.tail.ptr() {
        return None;
      }

      self.find_next_max_version(n, version, ignore_invalid_trailer)
    }
  }

  /// Returns the entry less than or equal to the given key, if it exists.
  ///
  /// e.g.
  ///
  /// - If k1 < k2 < k3, and key is equal to k3, then the entry contains k3 will be returned.
  /// - If k1 < k2 < k3, and k2 < key < k3, then the entry contains k2 will be returned.
  pub(crate) fn le<'a, 'b: 'a>(
    &'a self,
    version: Version,
    key: &'b [u8],
    ignore_invalid_trailer: bool,
  ) -> Option<<A::Node as Node>::Pointer> {
    unsafe {
      let (n, _) = self.find_near(Version::MIN, key, true, true, ignore_invalid_trailer); // find less or equal.

      let n = n?;
      if n.is_null() || n.ptr() == self.head.ptr() {
        return None;
      }

      self.find_prev_max_version(n, version, ignore_invalid_trailer)
    }
  }

  unsafe fn find_prev_max_version(
    &self,
    mut curr: <A::Node as Node>::Pointer,
    version: Version,
    ignore_invalid_trailer: bool,
  ) -> Option<<A::Node as Node>::Pointer> {
    let mut prev = self.get_prev(curr, 0, ignore_invalid_trailer);

    loop {
      let curr_node = curr.as_ref();
      let curr_key = curr_node.get_key(&self.arena);
      // if the current version is greater than the given version, we should return.
      let version_cmp = curr_node.version().cmp(&version);
      if version_cmp == cmp::Ordering::Greater {
        return None;
      }

      if prev.is_null() || prev.ptr() == self.head.ptr() {
        if let cmp::Ordering::Less | cmp::Ordering::Equal = version_cmp {
          return Some(curr);
        }

        return None;
      }

      let prev_node = prev.as_ref();
      let prev_key = prev_node.get_key(&self.arena);
      if self.cmp.compare(prev_key, curr_key) == cmp::Ordering::Less {
        return Some(curr);
      }

      let version_cmp = prev_node.version().cmp(&version);

      if version_cmp == cmp::Ordering::Equal {
        return Some(prev);
      }

      if version_cmp == cmp::Ordering::Greater {
        return Some(curr);
      }

      curr = prev;
      prev = self.get_prev(curr, 0, ignore_invalid_trailer);
    }
  }

  unsafe fn find_next_max_version(
    &self,
    mut curr: <A::Node as Node>::Pointer,
    version: Version,
    ignore_invalid_trailer: bool,
  ) -> Option<<A::Node as Node>::Pointer> {
    let mut next = self.get_next(curr, 0, ignore_invalid_trailer);

    loop {
      let curr_node = curr.as_ref();
      let curr_key = curr_node.get_key(&self.arena);
      // if the current version is less or equal to the given version, we should return.
      let version_cmp = curr_node.version().cmp(&version);
      if let cmp::Ordering::Less | cmp::Ordering::Equal = version_cmp {
        return Some(curr);
      }

      if next.is_null() || next.ptr() == self.head.ptr() {
        if let cmp::Ordering::Less | cmp::Ordering::Equal = version_cmp {
          return Some(curr);
        }

        return None;
      }

      let next_node = next.as_ref();
      let next_key = next_node.get_key(&self.arena);
      let version_cmp = next_node.version().cmp(&version);
      if self.cmp.compare(next_key, curr_key) == cmp::Ordering::Greater {
        if let cmp::Ordering::Less | cmp::Ordering::Equal = version_cmp {
          return Some(curr);
        }

        return None;
      }

      if let cmp::Ordering::Less | cmp::Ordering::Equal = version_cmp {
        if next.ptr() == self.tail.ptr() {
          return None;
        }

        return Some(next);
      }

      curr = next;
      next = self.get_next(curr, 0, ignore_invalid_trailer);
    }
  }

  /// finds the node near to key.
  /// If less=true, it finds rightmost node such that node.key < key (if allow_equal=false) or
  /// node.key <= key (if allow_equal=true).
  /// If less=false, it finds leftmost node such that node.key > key (if allow_equal=false) or
  /// node.key >= key (if allow_equal=true).
  /// Returns the node found. The bool returned is true if the node has key equal to given key.
  unsafe fn find_near(
    &self,
    version: Version,
    key: &[u8],
    less: bool,
    allow_equal: bool,
    ignore_invalid_trailer: bool,
  ) -> (Option<<A::Node as Node>::Pointer>, bool) {
    let mut x = self.head;
    let mut level = self.meta().height() as usize - 1;

    loop {
      // Assume x.key < key.
      let next = self.get_next(x, level, ignore_invalid_trailer);
      let is_next_null = next.is_null();

      if is_next_null || next.ptr() == self.tail.ptr() {
        // x.key < key < END OF LIST
        if level > 0 {
          // Can descend further to iterate closer to the end.
          level -= 1;
          continue;
        }

        // level == 0. Can't descend further. Let's return something that makes sense.
        if !less {
          return (None, false);
        }

        // Try to return x. Make sure it is not a head node.
        if x.ptr() == self.head.ptr() {
          return (None, false);
        }

        return (Some(x), false);
      }

      let next_node = next.as_ref();
      let next_key = next_node.get_key(&self.arena);
      let cmp = self
        .cmp
        .compare(key, next_key)
        .then_with(|| next_node.version().cmp(&version));

      match cmp {
        cmp::Ordering::Greater => {
          // x.key < next.key < key. We can continue to move right.
          x = next;
          continue;
        }
        cmp::Ordering::Equal => {
          // x.key < key == next.key.
          if allow_equal {
            return (Some(next), true);
          }

          if !less {
            // We want >, so go to base level to grab the next bigger node.
            return (Some(self.get_next(next, 0, ignore_invalid_trailer)), false);
          }

          // We want <. If not base level, we should go closer in the next level.
          if level > 0 {
            level -= 1;
            continue;
          }

          // On base level, Return x.
          return (Some(x), false);
        }
        // In other words, x.key < key < next.
        cmp::Ordering::Less => {
          if level > 0 {
            level -= 1;
            continue;
          }

          // On base level. Need to return something.
          if !less {
            return (Some(next), false);
          }

          // Try to return x. Make sure it is not a head node.
          if x.ptr() == self.head.ptr() {
            return (None, false);
          }

          return (Some(x), false);
        }
      }
    }
  }

  /// Find the place to insert the key.
  ///
  /// ## Safety:
  /// - All of splices in the inserter must be contains node ptrs are allocated by the current skip map.
  unsafe fn find_splice<'a, 'b: 'a>(
    &'a self,
    version: Version,
    key: &'b [u8],
    ins: &mut Inserter<<A::Node as Node>::Pointer>,
    returned_when_found: bool,
  ) -> (bool, Option<Pointer>, Option<<A::Node as Node>::Pointer>) {
    let list_height = self.meta().height() as u32;
    let mut level = 0;

    let mut prev = self.head;
    if ins.height < list_height {
      // Our cached height is less than the list height, which means there were
      // inserts that increased the height of the list. Recompute the splice from
      // scratch.
      ins.height = list_height;
      level = ins.height as usize;
    } else {
      // Our cached height is equal to the list height.
      while level < list_height as usize {
        let spl = &ins.spl[level];
        if self.get_next_allow_uncommitted(spl.prev, level).ptr() != spl.next.ptr() {
          level += 1;
          // One or more nodes have been inserted between the splice at this
          // level.
          continue;
        }

        if spl.prev.ptr() != self.head.ptr() && !self.key_is_after_node(spl.prev, version, key) {
          // Key lies before splice.
          level = list_height as usize;
          break;
        }

        if spl.next.ptr() != self.tail.ptr() && !self.key_is_after_node(spl.next, version, key) {
          // Key lies after splice.
          level = list_height as usize;
          break;
        }

        // The splice brackets the key!
        prev = spl.prev;
        break;
      }
    }

    let mut found = false;
    let mut found_key = None;
    for lvl in (0..level).rev() {
      let mut fr = self.find_splice_for_level(version, key, lvl, prev);
      if fr.splice.next.is_null() {
        fr.splice.next = self.tail;
      }

      found = fr.found;
      if let Some(key) = fr.found_key {
        found_key.get_or_insert(key);
      }
      if found && returned_when_found {
        return (found, found_key, fr.curr);
      }
      ins.spl[lvl] = fr.splice;
    }

    (found, found_key, None)
  }

  /// Find the splice for the given level.
  ///
  /// # Safety
  /// - `level` is less than `MAX_HEIGHT`.
  /// - `start` must be allocated by self's arena.
  unsafe fn find_splice_for_level(
    &self,
    version: Version,
    key: &[u8],
    level: usize,
    start: <A::Node as Node>::Pointer,
  ) -> FindResult<<A::Node as Node>::Pointer> {
    let mut prev = start;

    loop {
      // Assume prev.key < key.
      let next = self.get_next_allow_uncommitted(prev, level);
      if next.ptr() == self.tail.ptr() {
        // Tail node, so done.
        return FindResult {
          splice: Splice { prev, next },
          found: false,
          found_key: None,
          curr: None,
        };
      }

      // offset is not zero, so we can safely dereference the next node ptr.
      let next_node = next.as_ref();
      let next_key = next_node.get_key(&self.arena);

      let cmp = self.cmp.compare(key, next_key);

      let mut found_key = None;

      match cmp {
        cmp::Ordering::Equal => {
          found_key = Some(Pointer {
            offset: next_node.key_offset(),
            size: next_node.key_size(),
            height: Some(next_node.height()),
          });
        }
        cmp::Ordering::Greater | cmp::Ordering::Less if found_key.is_none() => {
          found_key = self.try_get_pointer(next_node, next_key, key);
        }
        _ => {}
      }

      match cmp.then_with(|| next_node.version().cmp(&version)) {
        // We are done for this level, since prev.key < key < next.key.
        cmp::Ordering::Less => {
          return FindResult {
            splice: Splice { prev, next },
            found: false,
            found_key,
            curr: None,
          };
        }
        // Keep moving right on this level.
        cmp::Ordering::Greater => prev = next,
        cmp::Ordering::Equal => {
          return FindResult {
            splice: Splice { prev, next },
            found: true,
            found_key,
            curr: Some(next),
          };
        }
      }
    }
  }

  fn try_get_pointer(&self, next_node: &A::Node, next_key: &[u8], key: &[u8]) -> Option<Pointer> {
    match self.opts.compression_policy() {
      CompressionPolicy::Fast => {
        if next_key.starts_with(key) {
          return Some(Pointer {
            offset: next_node.key_offset(),
            size: key.len() as u32,
            height: Some(next_node.height()),
          });
        }
      }
      CompressionPolicy::High => {
        if let Some(idx) = memchr::memmem::find(next_key, key) {
          return Some(Pointer {
            offset: next_node.key_offset() + idx as u32,
            size: key.len() as u32,
            height: Some(next_node.height()),
          });
        }
      }
    }
    None
  }

  /// ## Safety
  /// - The caller must ensure that the node is allocated by the arena.
  /// - The caller must ensure that the node is not null.
  unsafe fn key_is_after_node(
    &self,
    nd: <A::Node as Node>::Pointer,
    version: Version,
    key: &[u8],
  ) -> bool {
    let nd = &*nd.ptr();
    let nd_key = self
      .arena
      .get_bytes(nd.key_offset() as usize, nd.key_size() as usize);

    match self.cmp.compare(nd_key, key) {
      cmp::Ordering::Less => true,
      cmp::Ordering::Greater => false,
      cmp::Ordering::Equal => {
        matches!(version.cmp(&nd.version()), cmp::Ordering::Less)
      }
    }
  }

  #[inline]
  fn check_height_and_ro(&self, height: Height) -> Result<(), Error> {
    if self.arena.read_only() {
      return Err(Error::read_only());
    }

    let max_height = self.opts.max_height();

    if height > max_height {
      return Err(Error::invalid_height(height, max_height));
    }
    Ok(())
  }

  #[allow(clippy::too_many_arguments)]
  fn update<'a, 'b: 'a, E>(
    &'a self,
    version: Version,
    trailer: A::Trailer,
    height: u32,
    key: Key<'a, 'b, A>,
    value_builder: Option<ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>>,
    success: Ordering,
    failure: Ordering,
    mut ins: Inserter<'a, <A::Node as Node>::Pointer>,
    upsert: bool,
  ) -> Result<UpdateOk<'a, 'b, A>, Either<E, Error>> {
    let is_remove = key.is_remove();

    // Safety: a fresh new Inserter, so safe here
    let found_key = unsafe {
      let (found, found_key, ptr) = self.find_splice(version, key.as_ref(), &mut ins, true);
      if found_key.is_some() {
        key.on_fail(&self.arena);
      }

      if found {
        let node_ptr = ptr.expect("the NodePtr cannot be `None` when we found");
        let k = found_key.expect("the key cannot be `None` when we found");
        let old = VersionedEntryRef::from_node(node_ptr, &self.arena);

        if upsert {
          return self.upsert(
            old,
            node_ptr,
            &if is_remove {
              Key::remove_pointer(&self.arena, k)
            } else {
              Key::pointer(&self.arena, k)
            },
            trailer,
            value_builder,
            success,
            failure,
          );
        }

        return Ok(Either::Left(if old.is_removed() {
          None
        } else {
          Some(old)
        }));
      }

      found_key
    };

    #[cfg(all(test, feature = "std"))]
    if self.yield_now {
      // Add delay to make it easier to test race between this thread
      // and another thread that sees the intermediate state between
      // finding the splice and using it.
      std::thread::yield_now();
    }

    let k = match found_key {
      None => key,
      Some(k) => {
        if is_remove {
          Key::remove_pointer(&self.arena, k)
        } else {
          Key::pointer(&self.arena, k)
        }
      }
    };

    let (nd, mut deallocator) = self
      .new_node(version, height, &k, value_builder, trailer)
      .inspect_err(|_| {
        k.on_fail(&self.arena);
      })?;

    // self
    //   .link_in(
    //     UnlinkedNode::new(&self.arena, nd, height, version, deallocator),
    //     success,
    //     failure,
    //     upsert,
    //     ins,
    //   )
    //   .map_err(Either::Right)

    let is_removed = unsafe { nd.as_ref().get_value(&self.arena).is_none() };

    // We always insert from the base level and up. After you add a node in base
    // level, we cannot create a node in the level above because it would have
    // discovered the node in the base level.
    let mut invalid_data_splice = false;

    for i in 0..(height as usize) {
      let mut prev = ins.spl[i].prev;
      let mut next = ins.spl[i].next;

      if prev.is_null() {
        // New node increased the height of the skiplist, so assume that the
        // new level has not yet been populated.
        if !next.is_null() {
          panic!("next is expected to be nil, since prev is nil");
        }

        prev = self.head;
        next = self.tail;
      }

      // +----------------+     +------------+     +----------------+
      // |      prev      |     |     nd     |     |      next      |
      // | prevNextOffset |---->|            |     |                |
      // |                |<----| prevOffset |     |                |
      // |                |     | nextOffset |---->|                |
      // |                |     |            |<----| nextPrevOffset |
      // +----------------+     +------------+     +----------------+
      //
      // 1. Initialize prevOffset and nextOffset to point to prev and next.
      // 2. CAS prevNextOffset to repoint from next to nd.
      // 3. CAS nextPrevOffset to repoint from prev to nd.
      unsafe {
        loop {
          let prev_offset = prev.offset();
          let next_offset = next.offset();
          nd.write_tower(&self.arena, i, prev_offset, next_offset);

          // Check whether next has an updated link to prev. If it does not,
          // that can mean one of two things:
          //   1. The thread that added the next node hasn't yet had a chance
          //      to add the prev link (but will shortly).
          //   2. Another thread has added a new node between prev and next.
          //
          // Safety: we already check next is not null
          let next_prev_offset = next.prev_offset(&self.arena, i);
          if next_prev_offset != prev_offset {
            // Determine whether #1 or #2 is true by checking whether prev
            // is still pointing to next. As long as the atomic operations
            // have at least acquire/release semantics (no need for
            // sequential consistency), this works, as it is equivalent to
            // the "publication safety" pattern.
            let prev_next_offset = prev.next_offset(&self.arena, i);
            if prev_next_offset == next_offset {
              // Ok, case #1 is true, so help the other thread along by
              // updating the next node's prev link.

              let _ = next.cas_prev_offset(
                &self.arena,
                i,
                next_prev_offset,
                prev_offset,
                Ordering::SeqCst,
                Ordering::Acquire,
              );
            }
          }

          match prev.cas_next_offset(
            &self.arena,
            i,
            next.offset(),
            nd.offset(),
            Ordering::SeqCst,
            Ordering::Acquire,
          ) {
            Ok(_) => {
              // Managed to insert nd between prev and next, so update the next
              // node's prev link and go to the next level.
              #[cfg(all(test, feature = "std"))]
              if self.yield_now {
                // Add delay to make it easier to test race between this thread
                // and another thread that sees the intermediate state between
                // setting next and setting prev.
                std::thread::yield_now();
              }

              let _ = next.cas_prev_offset(
                &self.arena,
                i,
                prev_offset,
                nd.offset(),
                Ordering::SeqCst,
                Ordering::Acquire,
              );

              break;
            }

            Err(_) => {
              let unlinked_node = nd.as_ref();

              // CAS failed. We need to recompute prev and next. It is unlikely to
              // be helpful to try to use a different level as we redo the search,
              // because it is unlikely that lots of nodes are inserted between prev
              // and next.
              let fr =
                self.find_splice_for_level(version, unlinked_node.get_key(&self.arena), i, prev);
              if fr.found {
                if i != 0 {
                  panic!("how can another thread have inserted a node at a non-base level?");
                }

                let node_ptr = fr
                  .curr
                  .expect("the current should not be `None` when we found");
                let old = VersionedEntryRef::from_node(node_ptr, &self.arena);

                if upsert {
                  let curr = nd.as_ref();
                  let (new_value_offset, new_value_size) = curr.value_pointer().load();
                  deallocator.dealloc_node_and_key(&self.arena);

                  return self
                    .upsert_value(
                      old,
                      node_ptr,
                      &if is_removed {
                        Key::remove_pointer(&self.arena, fr.found_key.unwrap())
                      } else {
                        Key::pointer(&self.arena, fr.found_key.unwrap())
                      },
                      new_value_offset,
                      new_value_size,
                      success,
                      failure,
                    )
                    .map_err(Either::Right);
                }

                deallocator.dealloc(&self.arena);
                return Ok(Either::Left(if old.is_removed() {
                  None
                } else {
                  Some(old)
                }));
              }

              if let Some(p) = fr.found_key {
                // if key is already in the underlying allocator, we should deallocate the key
                // in deallocator, and let the underlying allocator reclaim it, so that we do not store the same key twice.
                if deallocator.key.is_some() {
                  let node = nd.as_mut();
                  node.set_key_offset(p.offset);
                  node
                    .set_key_size_and_height(encode_key_size_and_height(p.size, p.height.unwrap()));
                  deallocator.dealloc_key_by_ref(&self.arena)
                }
              }

              invalid_data_splice = true;
              prev = fr.splice.prev;
              next = fr.splice.next;
            }
          }
        }
      }
    }

    // If we had to recompute the splice for a level, invalidate the entire
    // cached splice.
    if invalid_data_splice {
      ins.height = 0;
    } else {
      // The splice was valid. We inserted a node between spl[i].prev and
      // spl[i].next. Optimistically update spl[i].prev for use in a subsequent
      // call to add.
      for i in 0..(height as usize) {
        ins.spl[i].prev = nd;
      }
    }
    let meta = self.meta();
    meta.increase_len();
    meta.update_max_version(version);
    meta.update_min_version(version);

    Ok(Either::Left(None))
  }

  #[allow(clippy::too_many_arguments)]
  unsafe fn upsert_value<'a, 'b: 'a>(
    &'a self,
    old: VersionedEntryRef<'a, A>,
    old_node_ptr: <A::Node as Node>::Pointer,
    key: &Key<'a, 'b, A>,
    value_offset: u32,
    value_size: u32,
    success: Ordering,
    failure: Ordering,
  ) -> Result<UpdateOk<'a, 'b, A>, Error> {
    match key {
      Key::Occupied(_) | Key::Vacant(_) | Key::Pointer { .. } => {
        let old_node = old_node_ptr.as_ref();
        old_node.update_value(&self.arena, value_offset, value_size);

        Ok(Either::Left(if old.is_removed() {
          None
        } else {
          Some(old)
        }))
      }
      Key::Remove(_) | Key::RemoveVacant(_) | Key::RemovePointer { .. } => {
        let node = old_node_ptr.as_ref();
        match node.clear_value(&self.arena, success, failure) {
          Ok(_) => Ok(Either::Left(None)),
          Err((offset, len)) => Ok(Either::Right(Err(
            VersionedEntryRef::from_node_with_pointer(
              old_node_ptr,
              &self.arena,
              ValuePartPointer::new(
                offset,
                A::align_offset::<A::Trailer>(offset) + mem::size_of::<A::Trailer>() as u32,
                len,
              ),
            ),
          ))),
        }
      }
    }
  }

  #[allow(clippy::too_many_arguments)]
  unsafe fn upsert<'a, 'b: 'a, E>(
    &'a self,
    old: VersionedEntryRef<'a, A>,
    old_node_ptr: <A::Node as Node>::Pointer,
    key: &Key<'a, 'b, A>,
    trailer: A::Trailer,
    value_builder: Option<ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>>,
    success: Ordering,
    failure: Ordering,
  ) -> Result<UpdateOk<'a, 'b, A>, Either<E, Error>> {
    match key {
      Key::Occupied(_) | Key::Vacant(_) | Key::Pointer { .. } => self
        .arena
        .allocate_and_update_value(old_node_ptr.as_ref(), trailer, value_builder.unwrap())
        .map(|_| Either::Left(if old.is_removed() { None } else { Some(old) })),
      Key::Remove(_) | Key::RemoveVacant(_) | Key::RemovePointer { .. } => {
        let node = old_node_ptr.as_ref();
        match node.clear_value(&self.arena, success, failure) {
          Ok(_) => Ok(Either::Left(None)),
          Err((offset, len)) => Ok(Either::Right(Err(
            VersionedEntryRef::from_node_with_pointer(
              old_node_ptr,
              &self.arena,
              ValuePartPointer::new(
                offset,
                A::align_offset::<A::Trailer>(offset) + mem::size_of::<A::Trailer>() as u32,
                len,
              ),
            ),
          ))),
        }
      }
    }
  }
}

/// A helper struct for caching splice information
pub struct Inserter<'a, P> {
  spl: [Splice<P>; super::MAX_HEIGHT],
  height: u32,
  _m: core::marker::PhantomData<&'a ()>,
}

impl<'a, P: NodePointer> Default for Inserter<'a, P> {
  #[inline]
  fn default() -> Self {
    Self {
      spl: [
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
      ],
      height: 0,
      _m: core::marker::PhantomData,
    }
  }
}

#[derive(Debug, Clone, Copy)]
struct Splice<P> {
  prev: P,
  next: P,
}

impl<P: NodePointer> Default for Splice<P> {
  #[inline]
  fn default() -> Self {
    Self {
      prev: P::NULL,
      next: P::NULL,
    }
  }
}

pub(crate) enum Key<'a, 'b: 'a, A> {
  Occupied(&'b [u8]),
  Vacant(VacantBuffer<'a>),
  Pointer {
    arena: &'a A,
    offset: u32,
    len: u32,
  },
  Remove(&'b [u8]),
  #[allow(dead_code)]
  RemoveVacant(VacantBuffer<'a>),
  RemovePointer {
    arena: &'a A,
    offset: u32,
    len: u32,
  },
}

impl<'a, 'b: 'a, A: Allocator> Key<'a, 'b, A> {
  #[inline]
  pub(crate) fn on_fail(&self, arena: &A) {
    match self {
      Self::Occupied(_) | Self::Remove(_) | Self::Pointer { .. } | Self::RemovePointer { .. } => {}
      Self::Vacant(key) | Self::RemoveVacant(key) => unsafe {
        arena.dealloc(key.offset, key.capacity() as u32);
      },
    }
  }
}

impl<'a, 'b: 'a, A> Key<'a, 'b, A> {
  /// Returns `true` if the key is a remove operation.
  #[inline]
  pub(crate) fn is_remove(&self) -> bool {
    matches!(
      self,
      Self::Remove(_) | Self::RemoveVacant(_) | Self::RemovePointer { .. }
    )
  }
}

impl<'a, 'b: 'a, A: Allocator> AsRef<[u8]> for Key<'a, 'b, A> {
  #[inline]
  fn as_ref(&self) -> &[u8] {
    match self {
      Self::Occupied(key) | Self::Remove(key) => key,
      Self::Vacant(key) | Self::RemoveVacant(key) => key.as_ref(),
      Self::Pointer { arena, offset, len } | Self::RemovePointer { arena, offset, len } => unsafe {
        arena.get_bytes(*offset as usize, *len as usize)
      },
    }
  }
}

impl<'a, 'b: 'a, A> Key<'a, 'b, A> {
  #[inline]
  const fn pointer(arena: &'a A, pointer: Pointer) -> Self {
    Self::Pointer {
      arena,
      offset: pointer.offset,
      len: pointer.size,
    }
  }

  #[inline]
  const fn remove_pointer(arena: &'a A, pointer: Pointer) -> Self {
    Self::RemovePointer {
      arena,
      offset: pointer.offset,
      len: pointer.size,
    }
  }
}

struct FindResult<P> {
  // both key and version are equal.
  found: bool,
  // only key is equal.
  found_key: Option<Pointer>,
  splice: Splice<P>,
  curr: Option<P>,
}