use core::{cmp, ptr::NonNull, sync::atomic::Ordering};

use std::boxed::Box;

use among::Among;
use dbutils::{
  buffer::VacantBuffer,
  equivalentor::{Ascend, Comparator},
};
use either::Either;
use rarena_allocator::Allocator as _;

use crate::{
  allocator::{Allocator, Deallocator, Header, Link, Node, NodePointer, Pointer, ValuePointer},
  encode_key_size_and_height,
  error::Error,
  random_height,
  traits::Constructable,
  types::{internal::ValuePointer as ValuePointerType, Height, KeyBuilder, ValueBuilder},
  CompressionPolicy, FindResult, Inserter, Splice, Version,
};

mod entry;
pub use entry::{EntryRef, VersionedEntryRef};

mod api;
pub(super) mod iterator;

type UpdateOk<'a, 'b, A, C> = Either<
  Option<VersionedEntryRef<'a, A, C>>,
  Result<VersionedEntryRef<'a, A, C>, VersionedEntryRef<'a, A, C>>,
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
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  on_disk: bool,
  /// If set to true by tests, then extra delays are added to make it easier to
  /// detect unusual race conditions.
  #[cfg(all(test, feature = "std"))]
  yield_now: bool,

  cmp: C,
}

unsafe impl<A, C> Send for SkipList<A, C>
where
  C: Send,
  A: Allocator + Send,
{
}

unsafe impl<A, C> Sync for SkipList<A, C>
where
  C: Sync,
  A: Allocator + Sync,
{
}

impl<A, C> Clone for SkipList<A, C>
where
  C: Clone,
  A: Allocator,
{
  fn clone(&self) -> Self {
    Self {
      arena: self.arena.clone(),
      meta: self.meta,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      on_disk: self.on_disk,
      head: self.head,
      tail: self.tail,
      data_offset: self.data_offset,
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
  #[allow(clippy::collapsible_if)]
  fn drop(&mut self) {
    if self.arena.refs() == 1 {
      if !self.arena.unify() {
        unsafe {
          let _ = Box::from_raw(self.meta.as_ptr());
        }
      }

      #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(miri)))]
      if self.arena.is_map() && self.arena.options().lock_meta() {
        let _ = unsafe { self.arena.munlock(0, self.arena.page_size()) };
      }
    }
  }
}

impl<A, C> SkipList<A, C>
where
  A: Allocator,
{
  #[inline]
  pub(crate) const fn meta(&self) -> &A::Header {
    // Safety: the pointer is well aligned and initialized.
    unsafe { self.meta.as_ref() }
  }
}

impl<A, C> Constructable for SkipList<A, C>
where
  A: Allocator,
{
  type Allocator = A;
  type Comparator = C;

  #[inline]
  fn allocator(&self) -> &Self::Allocator {
    &self.arena
  }

  #[inline]
  fn magic_version(&self) -> u16 {
    self.meta().magic_version()
  }

  #[inline]
  fn len(&self) -> usize {
    self.meta().len() as usize
  }

  #[inline]
  fn height(&self) -> u8 {
    self.meta().height()
  }

  #[inline]
  fn random_height(&self) -> crate::Height {
    random_height(self.arena.max_height())
  }

  #[inline]
  unsafe fn clear(&mut self) -> Result<(), crate::error::Error> {
    self.arena.clear()?;

    let options = self.arena.options();

    if self.arena.unify() {
      self.meta = self
        .arena
        .allocate_header(self.meta.as_ref().magic_version())?;
    } else {
      let magic_version = self.meta.as_ref().magic_version();
      let _ = Box::from_raw(self.meta.as_ptr());
      self.meta = NonNull::new_unchecked(Box::into_raw(Box::new(<A::Header as Header>::new(
        magic_version,
      ))));
    }

    let max_height: u8 = options.max_height().into();
    let head = self.arena.allocate_full_node(max_height)?;
    let tail = self.arena.allocate_full_node(max_height)?;

    // Safety:
    // We will always allocate enough space for the head node and the tail node.
    unsafe {
      // Link all head/tail levels together.
      for i in 0..(max_height as usize) {
        let head_link = head.tower(&self.arena, i);
        let tail_link = tail.tower(&self.arena, i);
        head_link.store_next_offset(tail.offset(), Ordering::Relaxed);
        tail_link.store_prev_offset(head.offset(), Ordering::Relaxed);
      }
    }

    self.head = head;
    self.tail = tail;
    Ok(())
  }

  #[inline]
  fn construct(
    arena: Self::Allocator,
    meta: core::ptr::NonNull<<Self::Allocator as crate::allocator::Sealed>::Header>,
    head: <<Self::Allocator as crate::allocator::Sealed>::Node as crate::allocator::Node>::Pointer,
    tail: <<Self::Allocator as crate::allocator::Sealed>::Node as crate::allocator::Node>::Pointer,
    data_offset: u32,
    cmp: Self::Comparator,
  ) -> Self {
    Self {
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      on_disk: arena.is_ondisk(),
      arena,
      meta,
      head,
      tail,
      data_offset,
      #[cfg(all(test, feature = "std"))]
      yield_now: false,
      cmp,
    }
  }
}

impl<A, C> SkipList<A, C>
where
  A: Allocator,
{
  fn new_node<'a, E>(
    &'a self,
    version: Version,
    height: u32,
    key: &Key<'a, '_, A>,
    value_builder: Option<ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, E>>>,
  ) -> Result<(<A::Node as Node>::Pointer, Deallocator), Either<E, Error>> {
    let (nd, deallocator) = match key {
      Key::Occupied(key) => {
        let klen = key.len();
        let kb = KeyBuilder::new(klen, |buf: &mut VacantBuffer<'_>| {
          buf.put_slice_unchecked(key);
          Ok(klen)
        });
        let vb = value_builder.unwrap();
        self
          .arena
          .allocate_entry_node::<(), E>(version, height, kb, vb)
          .map_err(Among::into_middle_right)?
      }
      Key::Vacant { buf: key, offset } => self.arena.allocate_value_node::<E>(
        version,
        height,
        key.len(),
        *offset,
        value_builder.unwrap(),
      )?,
      Key::Pointer { offset, len, .. } => self.arena.allocate_value_node::<E>(
        version,
        height,
        *len as usize,
        *offset,
        value_builder.unwrap(),
      )?,
      Key::Remove(key) => {
        let klen = key.len();
        self
          .arena
          .allocate_tombstone_node_with_key_builder::<()>(version, height, klen, |buf| {
            buf
              .put_slice(key)
              .expect("buffer must be large enough for key");
            Ok(klen)
          })
          .map_err(|e| Either::Right(e.unwrap_right()))?
      }
      Key::RemoveVacant { buf: key, offset } => self
        .arena
        .allocate_tombstone_node::<()>(version, height, *offset, key.len())
        .map_err(|e| Either::Right(e.unwrap_right()))?,
      Key::RemovePointer { offset, len, .. } => self
        .arena
        .allocate_tombstone_node::<()>(version, height, *offset, *len as usize)
        .map_err(|e| Either::Right(e.unwrap_right()))?,
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
{
  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[inline]
  unsafe fn get_prev(
    &self,
    nd: <A::Node as Node>::Pointer,
    height: usize,
  ) -> <A::Node as Node>::Pointer {
    if nd.is_null() {
      return <A::Node as Node>::Pointer::NULL;
    }

    if nd.offset() == self.head.offset() {
      return self.head;
    }

    let offset = nd.prev_offset(&self.arena, height);
    <A::Node as Node>::Pointer::new(offset, unsafe {
      NonNull::new_unchecked(self.arena.raw_mut_ptr().add(offset as usize))
    })
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[inline]
  unsafe fn get_next(
    &self,
    nptr: <A::Node as Node>::Pointer,
    height: usize,
  ) -> <A::Node as Node>::Pointer {
    if nptr.is_null() {
      return <A::Node as Node>::Pointer::NULL;
    }

    if nptr.offset() == self.tail.offset() {
      return self.tail;
    }

    let offset = nptr.next_offset(&self.arena, height);
    <A::Node as Node>::Pointer::new(offset, unsafe {
      NonNull::new_unchecked(self.arena.raw_mut_ptr().add(offset as usize))
    })
  }
}

impl<A, C> SkipList<A, C>
where
  A: Allocator,
  C: Comparator,
{
  unsafe fn move_to_prev<'a>(
    &'a self,
    nd: &mut <A::Node as Node>::Pointer,
    version: Version,
    contains_key: impl Fn(&[u8]) -> bool,
  ) -> Option<VersionedEntryRef<'a, A, C>> {
    loop {
      unsafe {
        if nd.is_null() || nd.offset() == self.head.offset() {
          return None;
        }

        if nd.version() > version {
          *nd = self.get_prev(*nd, 0);
          continue;
        }

        let nk = nd.get_key(&self.arena);
        if contains_key(nk) {
          let pointer = nd.get_value_pointer::<A>();
          let ent =
            VersionedEntryRef::from_node_with_pointer(version, *nd, self, pointer, Some(nk));
          return Some(ent);
        }

        *nd = self.get_prev(*nd, 0);
      }
    }
  }

  unsafe fn move_to_prev_maximum_version<'a>(
    &'a self,
    nd: &mut <A::Node as Node>::Pointer,
    version: Version,
    contains_key: impl Fn(&[u8]) -> bool,
  ) -> Option<VersionedEntryRef<'a, A, C>> {
    loop {
      unsafe {
        if nd.is_null() || nd.offset() == self.head.offset() {
          return None;
        }

        if nd.version() > version {
          *nd = self.get_prev(*nd, 0);
          continue;
        }

        let prev = self.get_prev(*nd, 0);

        if prev.is_null() || prev.offset() == self.head.offset() {
          // prev is null or the head, we should try to see if we can return the current node.
          if !nd.is_removed() {
            // the current node is valid, we should return it.
            let nk = nd.get_key(&self.arena);

            if contains_key(nk) {
              let pointer = nd.get_value_pointer::<A>();
              let ent =
                VersionedEntryRef::from_node_with_pointer(version, *nd, self, pointer, Some(nk));
              return Some(ent);
            }
          }

          return None;
        }

        // At this point, prev is not null and not the head.
        // if the prev's version is greater than the query version or the prev's key is different from the current key,
        // we should try to return the current node.
        if prev.version() > version || nd.get_key(&self.arena).ne(prev.get_key(&self.arena)) {
          let nk = nd.get_key(&self.arena);

          if !nd.is_removed() && contains_key(nk) {
            let pointer = nd.get_value_pointer::<A>();
            let ent =
              VersionedEntryRef::from_node_with_pointer(version, *nd, self, pointer, Some(nk));
            return Some(ent);
          }
        }

        *nd = prev;
      }
    }
  }

  unsafe fn move_to_next<'a>(
    &'a self,
    nd: &mut <A::Node as Node>::Pointer,
    version: Version,
    contains_key: impl Fn(&[u8]) -> bool,
  ) -> Option<VersionedEntryRef<'a, A, C>> {
    loop {
      unsafe {
        if nd.is_null() || nd.offset() == self.tail.offset() {
          return None;
        }

        if nd.version() > version {
          *nd = self.get_next(*nd, 0);
          continue;
        }

        let nk = nd.get_key(&self.arena);
        if contains_key(nk) {
          let pointer = nd.get_value_pointer::<A>();
          let ent =
            VersionedEntryRef::from_node_with_pointer(version, *nd, self, pointer, Some(nk));
          return Some(ent);
        }

        *nd = self.get_next(*nd, 0);
      }
    }
  }

  unsafe fn move_to_next_maximum_version<'a>(
    &'a self,
    nd: &mut <A::Node as Node>::Pointer,
    version: Version,
    contains_key: impl Fn(&[u8]) -> bool,
  ) -> Option<VersionedEntryRef<'a, A, C>> {
    loop {
      unsafe {
        if nd.is_null() || nd.offset() == self.tail.offset() {
          return None;
        }

        // if the current version is larger than the query version, we should move next to find a smaller version.
        let curr_version = nd.version();
        if curr_version > version {
          *nd = self.get_next(*nd, 0);
          continue;
        }

        // if the entry with largest version is removed, we should skip this key.
        if nd.is_removed() {
          let mut next = self.get_next(*nd, 0);
          let curr_key = nd.get_key(&self.arena);
          loop {
            if next.is_null() || next.offset() == self.tail.offset() {
              return None;
            }

            // if next's key is different from the current key, we should break the loop
            if next.get_key(&self.arena) != curr_key {
              *nd = next;
              break;
            }

            next = self.get_next(next, 0);
          }

          continue;
        }

        let nk = nd.get_key(&self.arena);
        if contains_key(nk) {
          let pointer = nd.get_value_pointer::<A>();
          let ent =
            VersionedEntryRef::from_node_with_pointer(version, *nd, self, pointer, Some(nk));
          return Some(ent);
        }

        *nd = self.get_next(*nd, 0);
      }
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
  ) -> (Option<<A::Node as Node>::Pointer>, bool) {
    let mut x = self.head;
    let mut level = self.meta().height() as usize - 1;

    loop {
      // Assume x.key < key.
      let next = self.get_next(x, level);
      let is_next_null = next.is_null();

      if is_next_null || next.offset() == self.tail.offset() {
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
        if x.offset() == self.head.offset() {
          return (None, false);
        }

        return (Some(x), false);
      }

      // let next_node = next.as_ref(&self.arena);
      let next_key = next.get_key(&self.arena);
      let cmp = self
        .cmp
        .compare(key, next_key)
        .then_with(|| next.version().cmp(&version));

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
            return (Some(self.get_next(next, 0)), false);
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
          if x.offset() == self.head.offset() {
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
    key: Either<&'a [u8], &'b [u8]>,
    ins: &mut Inserter<'a, <A::Node as Node>::Pointer>,
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
        if self.get_next(spl.prev, level).offset() != spl.next.offset() {
          level += 1;
          // One or more nodes have been inserted between the splice at this
          // level.
          continue;
        }

        if spl.prev.offset() != self.head.offset()
          && !self.key_is_after_node(spl.prev, version, key)
        {
          // Key lies before splice.
          level = list_height as usize;
          break;
        }

        if spl.next.offset() != self.tail.offset()
          && !self.key_is_after_node(spl.next, version, key)
        {
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
  /// ## Safety
  /// - `level` is less than `MAX_HEIGHT`.
  /// - `start` must be allocated by self's arena.
  unsafe fn find_splice_for_level<'a, 'b: 'a>(
    &'a self,
    version: Version,
    key: Either<&'a [u8], &'b [u8]>,
    level: usize,
    start: <A::Node as Node>::Pointer,
  ) -> FindResult<<A::Node as Node>::Pointer> {
    let mut prev = start;

    loop {
      // Assume prev.key < key.
      let next = self.get_next(prev, level);
      if next.offset() == self.tail.offset() {
        // Tail node, so done.
        return FindResult {
          splice: Splice { prev, next },
          found: false,
          found_key: None,
          curr: None,
        };
      }

      // offset is not zero, so we can safely dereference the next node ptr.
      // let next_node = next.as_ref(&self.arena);
      let next_key = next.get_key(&self.arena);

      let cmp = Key::<'a, '_, A>::compare(key, next_key, &self.cmp);

      let mut found_key = None;

      match cmp {
        cmp::Ordering::Equal => {
          found_key = Some(Pointer {
            offset: next.key_offset(),
            size: next.key_size(),
            height: Some(next.height()),
          });
        }
        cmp::Ordering::Greater | cmp::Ordering::Less if found_key.is_none() => {
          found_key = self.try_get_pointer(&next, next_key, key);
        }
        _ => {}
      }

      match cmp.then_with(|| next.version().cmp(&version)) {
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

  fn try_get_pointer<'a, 'b: 'a>(
    &'a self,
    next_node: &<A::Node as Node>::Pointer,
    next_key: &[u8],
    key: Either<&'a [u8], &'b [u8]>,
  ) -> Option<Pointer> {
    if let Either::Left(key) | Either::Right(key) = key {
      match self.arena.options().compression_policy() {
        CompressionPolicy::Fast => {
          if next_key.starts_with(key) {
            return Some(Pointer {
              offset: next_node.key_offset(),
              size: key.len() as u32,
              height: Some(next_node.height()),
            });
          }
        }
        #[cfg(feature = "experimental")]
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
    }

    None
  }

  /// ## Safety
  /// - The caller must ensure that the node is allocated by the arena.
  /// - The caller must ensure that the node is not null.
  unsafe fn key_is_after_node<'a, 'b: 'a>(
    &'a self,
    nd: <A::Node as Node>::Pointer,
    version: Version,
    key: Either<&'a [u8], &'b [u8]>,
  ) -> bool {
    let nd_key = self
      .arena
      .get_bytes(nd.key_offset() as usize, nd.key_size() as usize);
    match Key::<'a, '_, A>::compare(key, nd_key, &self.cmp) {
      cmp::Ordering::Less => false,
      cmp::Ordering::Greater => true,
      cmp::Ordering::Equal => {
        matches!(version.cmp(&nd.version()), cmp::Ordering::Less)
      }
    }
  }

  #[inline]
  fn validate(&self, height: Height, klen: usize, vlen: usize) -> Result<(), Error> {
    if self.arena.read_only() {
      return Err(Error::read_only());
    }

    let max_height = self.arena.max_height();
    if height < 1 || height > max_height {
      return Err(Error::invalid_height(height, max_height));
    }

    let max_key_size = self.arena.max_key_size();
    if klen > max_key_size {
      return Err(Error::invalid_key_size(klen, max_key_size));
    }

    let vlen = if vlen == <<A::Node as Node>::ValuePointer as ValuePointer>::REMOVE as usize {
      0
    } else {
      vlen
    };

    let max_value_size = self.arena.max_value_size();
    if vlen > max_value_size {
      return Err(Error::invalid_value_size(vlen, max_value_size));
    }

    let entry_size = (vlen as u64 + klen as u64) + <A::Node as Node>::size(height.to_u8()) as u64;
    if entry_size > u32::MAX as u64 {
      return Err(Error::invalid_entry_size(entry_size, u32::MAX as u64));
    }

    Ok(())
  }

  #[allow(clippy::too_many_arguments)]
  fn update<'a, 'b: 'a, E>(
    &'a self,
    version: Version,
    height: u32,
    key: Key<'a, 'b, A>,
    value_builder: Option<ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, E>>>,
    success: Ordering,
    failure: Ordering,
    mut ins: Inserter<'a, <A::Node as Node>::Pointer>,
    upsert: bool,
  ) -> Result<UpdateOk<'a, 'b, A, C>, Either<E, Error>> {
    let is_remove = key.is_remove();

    // Safety: a fresh new Inserter, so safe here
    let found_key = unsafe {
      let (found, found_key, ptr) = self.find_splice(version, key.as_slice(), &mut ins, true);
      if found_key.is_some() {
        key.on_fail(&self.arena);
      }

      if found {
        let node_ptr = ptr.expect("the NodePtr cannot be `None` when we found");
        let k = found_key.expect("the key cannot be `None` when we found");
        let old = VersionedEntryRef::from_node(version, node_ptr, self, None);

        if upsert {
          return self.upsert(
            version,
            old,
            node_ptr,
            &if is_remove {
              Key::remove_pointer(&self.arena, k)
            } else {
              Key::pointer(&self.arena, k)
            },
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

    let (unlinked_node, mut deallocator) = self
      .new_node(version, height, &k, value_builder)
      .inspect_err(|_| {
        k.on_fail(&self.arena);
      })?;

    let is_removed = unsafe { unlinked_node.get_value(&self.arena).is_none() };

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
          unlinked_node.write_tower(&self.arena, i, prev_offset, next_offset);

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
            unlinked_node.offset(),
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
                unlinked_node.offset(),
                Ordering::SeqCst,
                Ordering::Acquire,
              );

              break;
            }

            Err(_) => {
              // let unlinked_node = nd;

              // CAS failed. We need to recompute prev and next. It is unlikely to
              // be helpful to try to use a different level as we redo the search,
              // because it is unlikely that lots of nodes are inserted between prev
              // and next.
              let fr = self.find_splice_for_level(
                version,
                Either::Left(unlinked_node.get_key(&self.arena)),
                i,
                prev,
              );
              if fr.found {
                if i != 0 {
                  panic!("how can another thread have inserted a node at a non-base level?");
                }

                let node_ptr = fr
                  .curr
                  .expect("the current should not be `None` when we found");
                let old = VersionedEntryRef::from_node(version, node_ptr, self, None);

                if upsert {
                  // let curr = nd.as_ref(&self.arena);
                  let (new_value_offset, new_value_size) = unlinked_node.value_pointer().load();
                  deallocator.dealloc_node_and_key(&self.arena);

                  return self
                    .upsert_value(
                      version,
                      old,
                      node_ptr,
                      &if is_removed {
                        Key::<A>::remove_pointer(&self.arena, fr.found_key.unwrap())
                      } else {
                        Key::<A>::pointer(&self.arena, fr.found_key.unwrap())
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
                  unlinked_node.set_key_offset(p.offset);
                  unlinked_node
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
        ins.spl[i].prev = unlinked_node;
      }
    }
    let meta = self.meta();
    meta.increase_len();
    meta.update_maximum_version(version);
    meta.update_minimum_version(version);

    Ok(Either::Left(None))
  }

  #[allow(clippy::too_many_arguments)]
  unsafe fn upsert_value<'a, 'b: 'a>(
    &'a self,
    version: Version,
    old: VersionedEntryRef<'a, A, C>,
    old_node: <A::Node as Node>::Pointer,
    key: &Key<'a, 'b, A>,
    value_offset: u32,
    value_size: u32,
    success: Ordering,
    failure: Ordering,
  ) -> Result<UpdateOk<'a, 'b, A, C>, Error> {
    match key {
      Key::Occupied(_) | Key::Vacant { .. } | Key::Pointer { .. } => {
        old_node.update_value(&self.arena, value_offset, value_size);

        Ok(Either::Left(if old.is_removed() {
          None
        } else {
          Some(old)
        }))
      }
      Key::Remove(_) | Key::RemoveVacant { .. } | Key::RemovePointer { .. } => {
        match old_node.clear_value(&self.arena, success, failure) {
          Ok(_) => Ok(Either::Left(None)),
          Err((offset, len)) => Ok(Either::Right(Err(
            VersionedEntryRef::from_node_with_pointer(
              version,
              old_node,
              self,
              ValuePointerType::new(offset, len),
              None,
            ),
          ))),
        }
      }
    }
  }

  #[allow(clippy::too_many_arguments)]
  unsafe fn upsert<'a, 'b: 'a, E>(
    &'a self,
    version: Version,
    old: VersionedEntryRef<'a, A, C>,
    old_node: <A::Node as Node>::Pointer,
    key: &Key<'a, 'b, A>,
    value_builder: Option<ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, E>>>,
    success: Ordering,
    failure: Ordering,
  ) -> Result<UpdateOk<'a, 'b, A, C>, Either<E, Error>> {
    match key {
      Key::Occupied(_) | Key::Vacant { .. } | Key::Pointer { .. } => self
        .arena
        .allocate_and_update_value(&old_node, value_builder.unwrap())
        .map(|_| Either::Left(if old.is_removed() { None } else { Some(old) })),
      Key::Remove(_) | Key::RemoveVacant { .. } | Key::RemovePointer { .. } => {
        match old_node.clear_value(&self.arena, success, failure) {
          Ok(_) => Ok(Either::Left(None)),
          Err((offset, len)) => Ok(Either::Right(Err(
            VersionedEntryRef::from_node_with_pointer(
              version,
              old_node,
              self,
              ValuePointerType::new(offset, len),
              None,
            ),
          ))),
        }
      }
    }
  }
}

pub(crate) enum Key<'a, 'b: 'a, A> {
  Occupied(&'b [u8]),
  Vacant {
    buf: VacantBuffer<'a>,
    offset: u32,
  },
  Pointer {
    arena: &'a A,
    offset: u32,
    len: u32,
  },
  Remove(&'b [u8]),
  #[allow(dead_code)]
  RemoveVacant {
    buf: VacantBuffer<'a>,
    offset: u32,
  },
  RemovePointer {
    arena: &'a A,
    offset: u32,
    len: u32,
  },
}

impl<A: Allocator> Key<'_, '_, A> {
  #[inline]
  pub(crate) fn on_fail(&self, arena: &A) {
    match self {
      Self::Occupied(_) | Self::Remove(_) | Self::Pointer { .. } | Self::RemovePointer { .. } => {}
      Self::Vacant { buf, offset } | Self::RemoveVacant { buf, offset } => unsafe {
        arena.dealloc(*offset, buf.capacity() as u32);
      },
    }
  }
}

impl<'a, 'b: 'a, A: Allocator> Key<'a, 'b, A> {
  #[inline]
  fn as_slice(&self) -> Either<&'a [u8], &'b [u8]> {
    match self {
      Self::Occupied(key) | Self::Remove(key) => Either::Right(key),
      Self::Vacant { buf, .. } | Self::RemoveVacant { buf, .. } => Either::Left(buf.as_slice()),
      Self::Pointer { arena, offset, len } | Self::RemovePointer { arena, offset, len } => unsafe {
        Either::Left(arena.get_bytes(*offset as usize, *len as usize))
      },
    }
  }
}

impl<'a, 'b: 'a, A> Key<'a, 'b, A>
where
  A: Allocator,
{
  #[inline]
  fn compare<C>(this: Either<&'a [u8], &'b [u8]>, other: &'a [u8], cmp: &C) -> cmp::Ordering
  where
    C: Comparator,
  {
    match this {
      Either::Left(key) | Either::Right(key) => cmp.compare(key, other),
    }
  }
}

impl<A> Key<'_, '_, A> {
  /// Returns `true` if the key is a remove operation.
  #[inline]
  pub(crate) fn is_remove(&self) -> bool {
    matches!(
      self,
      Self::Remove(_) | Self::RemoveVacant { .. } | Self::RemovePointer { .. }
    )
  }
}

impl<'a, A> Key<'a, '_, A> {
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
