use core::{
  cmp,
  convert::Infallible,
  ops::{Bound, RangeBounds},
};

use crate::{Key, Trailer, VacantBuffer};

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
use super::{invalid_data, MmapOptions, OpenOptions};

use super::{arena::Arena, sync::Ordering, Ascend, Comparator, MAX_HEIGHT};

mod api;

mod node;
use either::Either;
use node::{Node, NodePtr};
mod error;
pub use error::Error;
mod entry;
pub use entry::*;
mod iterator;
pub use iterator::*;

#[cfg(all(test, not(loom)))]
mod tests;

#[cfg(all(test, loom))]
mod loom;

type UpdateOk<'a, 'b, T, C> = Either<
  Option<VersionedEntryRef<'a, T, C>>,
  Result<VersionedEntryRef<'a, T, C>, VersionedEntryRef<'a, T, C>>,
>;

/// A fast, cocnurrent map implementation based on skiplist that supports forward
/// and backward iteration. Keys and values are immutable once added to the skipmap and
/// deletion is not supported. Instead, higher-level code is expected to add new
/// entries that shadow existing entries and perform deletion via tombstones. It
/// is up to the user to process these shadow entries and tombstones
/// appropriately during retrieval.
#[derive(Debug)]
pub struct SkipMap<T = u64, C = Ascend> {
  arena: Arena,
  head: NodePtr<T>,
  tail: NodePtr<T>,

  /// If set to true by tests, then extra delays are added to make it easier to
  /// detect unusual race conditions.
  #[cfg(all(test, feature = "std"))]
  yield_now: bool,

  ro: bool,

  cmp: C,
}

// Safety: SkipMap is Sync and Send
unsafe impl<T: Send, C: Comparator + Send> Send for SkipMap<T, C> {}
unsafe impl<T: Sync, C: Comparator + Sync> Sync for SkipMap<T, C> {}

impl<T, C: Clone> Clone for SkipMap<T, C> {
  fn clone(&self) -> Self {
    Self {
      arena: self.arena.clone(),
      head: self.head,
      tail: self.tail,
      ro: self.ro,
      #[cfg(all(test, feature = "std"))]
      yield_now: self.yield_now,
      cmp: self.cmp.clone(),
    }
  }
}

impl<T, C> SkipMap<T, C> {
  fn new_in(arena: Arena, cmp: C, ro: bool) -> Result<Self, Error> {
    if ro {
      let (ptr, offset) = arena.head_ptr::<T>(Node::<T>::MAX_NODE_SIZE as u32, Node::<T>::ALIGN);
      let head = NodePtr::new(ptr, offset);
      let (ptr, offset) = arena.tail_ptr::<T>(Node::<T>::MAX_NODE_SIZE as u32, Node::<T>::ALIGN);
      let tail = NodePtr::new(ptr, offset);
      return Ok(Self::construct(arena, head, tail, ro, cmp));
    }

    let head = Node::new_empty_node_ptr(&arena)?;
    let tail = Node::new_empty_node_ptr(&arena)?;

    // Safety:
    // We will always allocate enough space for the head node and the tail node.
    unsafe {
      // Link all head/tail levels together.
      for i in 0..MAX_HEIGHT {
        let head_link = head.tower(&arena, i);
        let tail_link = tail.tower(&arena, i);
        head_link.next_offset.store(tail.offset, Ordering::Relaxed);
        tail_link.prev_offset.store(head.offset, Ordering::Relaxed);
      }
    }

    Ok(Self::construct(arena, head, tail, ro, cmp))
  }

  #[inline]
  fn construct(arena: Arena, head: NodePtr<T>, tail: NodePtr<T>, ro: bool, cmp: C) -> Self {
    Self {
      arena,
      head,
      tail,
      ro,
      #[cfg(all(test, feature = "std"))]
      yield_now: false,
      cmp,
    }
  }
}

impl<T: Trailer, C> SkipMap<T, C> {
  fn new_node<'a, 'b: 'a, E>(
    &'a self,
    key: &Key<'a, 'b>,
    trailer: T,
    value_size: u32,
    f: impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>,
  ) -> Result<(NodePtr<T>, u32), Either<E, Error>> {
    let height = super::random_height();
    let nd = match key {
      Key::Occupied(key) => Node::new_node_ptr(&self.arena, height, key, trailer, value_size, f)?,
      Key::Vacant(key) => Node::new_node_ptr_with_key(
        &self.arena,
        height,
        key.offset,
        key.len() as u16,
        trailer,
        value_size,
        f,
      )?,
      Key::Remove(key) => {
        Node::new_remove_node_ptr(&self.arena, height, key, trailer).map_err(Either::Right)?
      }
      Key::RemoveVacant(key) => Node::new_remove_node_ptr_with_key(
        &self.arena,
        height,
        key.offset,
        key.len() as u16,
        trailer,
      )
      .map_err(Either::Right)?,
    };

    // Try to increase self.height via CAS.
    let mut list_height = self.height();
    while height > list_height {
      match self.arena.atomic_height().compare_exchange_weak(
        list_height,
        height,
        Ordering::SeqCst,
        Ordering::Acquire,
      ) {
        // Successfully increased skiplist.height.
        Ok(_) => break,
        Err(h) => list_height = h,
      }
    }
    Ok((nd, height))
  }
}

impl<T: Trailer, C: Comparator> SkipMap<T, C> {
  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[inline]
  unsafe fn get_prev(&self, nd: NodePtr<T>, height: usize) -> NodePtr<T> {
    if nd.is_null() {
      return NodePtr::NULL;
    }

    let offset = nd.prev_offset(&self.arena, height);
    let ptr = self.arena.get_pointer(offset as usize);
    NodePtr::new(ptr, offset)
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[inline]
  unsafe fn get_next(&self, nptr: NodePtr<T>, height: usize) -> NodePtr<T> {
    if nptr.is_null() {
      return NodePtr::NULL;
    }
    let offset = nptr.next_offset(&self.arena, height);
    let ptr = self.arena.get_pointer(offset as usize);
    NodePtr::new(ptr, offset)
  }

  /// Returns the first entry in the map.
  fn first_in(&self, version: u64) -> Option<NodePtr<T>> {
    // Safety: head node was definitely allocated by self.arena
    let nd = unsafe { self.get_next(self.head, 0) };

    if nd.is_null() || nd.ptr == self.tail.ptr {
      return None;
    }

    unsafe {
      let node = nd.as_ptr();
      let curr_key = node.get_key(&self.arena);
      self.ge(version, curr_key)
    }
  }

  /// Returns the last entry in the map.
  fn last_in(&self, version: u64) -> Option<NodePtr<T>> {
    // Safety: tail node was definitely allocated by self.arena
    let nd = unsafe { self.get_prev(self.tail, 0) };

    if nd.is_null() || nd.ptr == self.head.ptr {
      return None;
    }

    unsafe {
      let node = nd.as_ptr();
      let curr_key = node.get_key(&self.arena);
      self.le(version, curr_key)
    }
  }

  /// Returns the entry greater or equal to the given key, if it exists.
  ///
  /// e.g.
  ///
  /// - If k1 < k2 < k3, key is equal to k1, then the entry contains k2 will be returned.
  /// - If k1 < k2 < k3, and k1 < key < k2, then the entry contains k2 will be returned.
  fn gt<'a, 'b: 'a>(&'a self, version: u64, key: &'b [u8]) -> Option<NodePtr<T>> {
    unsafe {
      let (n, _) = self.find_near(u64::MIN, key, false, false); // find the key with the max version.

      let n = n?;

      if n.is_null() || n.ptr == self.tail.ptr {
        return None;
      }

      self.find_next_max_version(n, version)
    }
  }

  /// Returns the entry less than the given key, if it exists.
  ///
  /// e.g.
  ///
  /// - If k1 < k2 < k3, and key is equal to k3, then the entry contains k2 will be returned.
  /// - If k1 < k2 < k3, and k2 < key < k3, then the entry contains k2 will be returned.
  fn lt<'a, 'b: 'a>(&'a self, version: u64, key: &'b [u8]) -> Option<NodePtr<T>> {
    unsafe {
      let (n, _) = self.find_near(u64::MAX, key, true, false); // find less or equal.

      let n = n?;
      if n.is_null() || n.ptr == self.head.ptr {
        return None;
      }

      self.find_prev_max_version(n, version)
    }
  }

  /// Returns the entry greater than or equal to the given key, if it exists.
  ///
  /// e.g.
  ///
  /// - If k1 < k2 < k3, key is equal to k1, then the entry contains k1 will be returned.
  /// - If k1 < k2 < k3, and k1 < key < k2, then the entry contains k2 will be returned.
  fn ge<'a, 'b: 'a>(&'a self, version: u64, key: &'b [u8]) -> Option<NodePtr<T>> {
    unsafe {
      // TODO: optimize find_near implementation, so that we can directly use version instead of u64::MIN
      let (n, _) = self.find_near(u64::MAX, key, false, true); // find the key with the max version.

      let n = n?;

      if n.is_null() || n.ptr == self.tail.ptr {
        return None;
      }

      self.find_next_max_version(n, version)
    }
  }

  /// Returns the entry less than or equal to the given key, if it exists.
  ///
  /// e.g.
  ///
  /// - If k1 < k2 < k3, and key is equal to k3, then the entry contains k3 will be returned.
  /// - If k1 < k2 < k3, and k2 < key < k3, then the entry contains k2 will be returned.
  fn le<'a, 'b: 'a>(&'a self, version: u64, key: &'b [u8]) -> Option<NodePtr<T>> {
    unsafe {
      let (n, _) = self.find_near(u64::MIN, key, true, true); // find less or equal.

      let n = n?;
      if n.is_null() || n.ptr == self.head.ptr {
        return None;
      }

      self.find_prev_max_version(n, version)
    }
  }

  unsafe fn find_prev_max_version(&self, mut curr: NodePtr<T>, version: u64) -> Option<NodePtr<T>> {
    let mut prev = self.get_prev(curr, 0);

    loop {
      let curr_node = curr.as_ptr();
      let curr_key = curr_node.get_key(&self.arena);
      // if the current version is greater than the given version, we should return.
      let version_cmp = curr_node.get_trailer(&self.arena).version().cmp(&version);
      if version_cmp == cmp::Ordering::Greater {
        return None;
      }

      if prev.is_null() || prev.ptr == self.head.ptr {
        if let cmp::Ordering::Less | cmp::Ordering::Equal = version_cmp {
          return Some(curr);
        }

        return None;
      }

      let prev_node = prev.as_ptr();
      let prev_key = prev_node.get_key(&self.arena);
      if self.cmp.compare(prev_key, curr_key) == cmp::Ordering::Less {
        return Some(curr);
      }

      let version_cmp = prev_node.get_trailer(&self.arena).version().cmp(&version);

      if version_cmp == cmp::Ordering::Equal {
        return Some(prev);
      }

      if version_cmp == cmp::Ordering::Greater {
        return Some(curr);
      }

      curr = prev;
      prev = self.get_prev(curr, 0);
    }
  }

  unsafe fn find_next_max_version(&self, mut curr: NodePtr<T>, version: u64) -> Option<NodePtr<T>> {
    let mut next = self.get_next(curr, 0);

    loop {
      let curr_node = curr.as_ptr();
      let curr_key = curr_node.get_key(&self.arena);
      // if the current version is less or equal to the given version, we should return.
      let version_cmp = curr_node.get_trailer(&self.arena).version().cmp(&version);
      if let cmp::Ordering::Less | cmp::Ordering::Equal = version_cmp {
        return Some(curr);
      }

      if next.is_null() || next.ptr == self.head.ptr {
        if let cmp::Ordering::Less | cmp::Ordering::Equal = version_cmp {
          return Some(curr);
        }

        return None;
      }

      let next_node = next.as_ptr();
      let next_key = next_node.get_key(&self.arena);
      let version_cmp = next_node.get_trailer(&self.arena).version().cmp(&version);
      if self.cmp.compare(next_key, curr_key) == cmp::Ordering::Greater {
        if let cmp::Ordering::Less | cmp::Ordering::Equal = version_cmp {
          return Some(curr);
        }

        return None;
      }

      if let cmp::Ordering::Less | cmp::Ordering::Equal = version_cmp {
        if next.ptr == self.tail.ptr {
          return None;
        }

        return Some(next);
      }

      curr = next;
      next = self.get_next(curr, 0);
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
    version: u64,
    key: &[u8],
    less: bool,
    allow_equal: bool,
  ) -> (Option<NodePtr<T>>, bool) {
    let mut x = self.head;
    let mut level = self.height() as usize - 1;

    loop {
      // Assume x.key < key.
      let next = self.get_next(x, level);
      if next.is_null() || next.ptr == self.tail.ptr {
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
        if x.ptr == self.head.ptr {
          return (None, false);
        }

        return (Some(x), false);
      }

      let next_node = next.as_ptr();
      let next_key = next_node.get_key(&self.arena);
      let cmp = self
        .cmp
        .compare(key, next_key)
        .then_with(|| next_node.get_trailer(&self.arena).version().cmp(&version));

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
          if x.ptr == self.head.ptr {
            return (None, false);
          }

          return (Some(x), false);
        }
      }
    }
  }

  /// ## Safety:
  /// - All of splices in the inserter must be contains node ptrs are allocated by the current skip map.
  unsafe fn find_splice<'a, 'b: 'a>(
    &'a self,
    version: u64,
    key: &'b [u8],
    ins: &mut Inserter<T>,
    returned_when_found: bool,
  ) -> (bool, Option<NodePtr<T>>) {
    let list_height = self.height();
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
        if self.get_next(spl.prev, level).ptr != spl.next.ptr {
          level += 1;
          // One or more nodes have been inserted between the splice at this
          // level.
          continue;
        }

        if spl.prev.ptr != self.head.ptr && !self.key_is_after_node(spl.prev, version, key) {
          // Key lies before splice.
          level = list_height as usize;
          break;
        }

        if spl.next.ptr != self.tail.ptr && !self.key_is_after_node(spl.next, version, key) {
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
    for lvl in (0..level).rev() {
      let mut fr = self.find_splice_for_level(version, key, lvl, prev);
      if fr.splice.next.is_null() {
        fr.splice.next = self.tail;
      }
      found = fr.found;
      if found && returned_when_found {
        return (found, fr.curr);
      }
      ins.spl[lvl] = fr.splice;
    }

    (found, None)
  }

  /// ## Safety
  /// - `level` is less than `MAX_HEIGHT`.
  /// - `start` must be allocated by self's arena.
  unsafe fn find_splice_for_level(
    &self,
    version: u64,
    key: &[u8],
    level: usize,
    start: NodePtr<T>,
  ) -> FindResult<T> {
    let mut prev = start;

    loop {
      // Assume prev.key < key.
      let next = self.get_next(prev, level);
      if next.ptr == self.tail.ptr {
        // Tail node, so done.
        return FindResult {
          splice: Splice { prev, next },
          found: false,
          curr: None,
        };
      }

      // offset is not zero, so we can safely dereference the next node ptr.
      let next_node = next.as_ptr();
      let next_key = next_node.get_key(&self.arena);

      match self
        .cmp
        .compare(key, next_key)
        .then_with(|| next_node.get_trailer(&self.arena).version().cmp(&version))
      {
        // We are done for this level, since prev.key < key < next.key.
        cmp::Ordering::Less => {
          return FindResult {
            splice: Splice { prev, next },
            found: false,
            curr: None,
          };
        }
        // Keep moving right on this level.
        cmp::Ordering::Greater => prev = next,
        cmp::Ordering::Equal => {
          // Internal key equality.
          return FindResult {
            splice: Splice { prev, next },
            found: true,
            curr: Some(next),
          };
        }
      }
    }
  }

  /// ## Safety
  /// - The caller must ensure that the node is allocated by the arena.
  /// - The caller must ensure that the node is not null.
  unsafe fn key_is_after_node(&self, nd: NodePtr<T>, version: u64, key: &[u8]) -> bool {
    let nd = &*nd.ptr;
    let nd_key = self
      .arena
      .get_bytes(nd.key_offset as usize, nd.key_size as usize);

    match self
      .cmp
      .compare(nd_key, key)
      // .then_with(|| version.cmp(&nd.version))
    {
      cmp::Ordering::Less => true,
      cmp::Ordering::Greater => false,
      cmp::Ordering::Equal => {
        matches!(version.cmp(&nd.get_trailer(&self.arena).version()), cmp::Ordering::Less)
      }
    }
  }

  fn fetch_vacant_key<'a, 'b: 'a, E>(
    &'a self,
    key_size: u16,
    key: impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>,
  ) -> Result<VacantBuffer<'a>, Either<E, Error>> {
    let (key_offset, key_size) = self.arena.alloc_key(key_size).map_err(|e| {
      self.arena.incr_discard(key_size as u32);
      Either::Right(e.into())
    })?;

    let mut vk = unsafe {
      VacantBuffer::new(
        key_size as usize,
        key_offset,
        self
          .arena
          .get_bytes_mut(key_offset as usize, key_size as usize),
      )
    };
    key(&mut vk)
      .map_err(|e| {
        self.arena.incr_discard(key_size as u32);
        Either::Left(e)
      })
      .map(|_| vk)
  }

  #[allow(clippy::too_many_arguments)]
  fn update<'a, 'b: 'a, E>(
    &'a self,
    trailer: T,
    key: Key<'a, 'b>,
    value_size: u32,
    f: impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E> + Copy,
    success: Ordering,
    failure: Ordering,
    ins: &mut Inserter<T>,
    upsert: bool,
  ) -> Result<UpdateOk<'a, 'b, T, C>, Either<E, Error>> {
    let version = trailer.version();

    // Safety: a fresh new Inserter, so safe here
    unsafe {
      let (found, ptr) = self.find_splice(version, key.as_ref(), ins, true);
      if found {
        let node_ptr = ptr.expect("the NodePtr cannot be `None` when we found");
        let old = VersionedEntryRef::from_node(node_ptr, self);

        key.on_fail(&self.arena);

        if upsert {
          return self.upsert(
            old, node_ptr, &key, trailer, value_size, f, success, failure,
          );
        }

        return Ok(Either::Left(if old.is_removed() {
          None
        } else {
          Some(old)
        }));
      }
    }

    #[cfg(all(test, feature = "std"))]
    if self.yield_now {
      // Add delay to make it easier to test race between this thread
      // and another thread that sees the intermediate state between
      // finding the splice and using it.
      std::thread::yield_now();
    }

    let (nd, height) = self.new_node(&key, trailer, value_size, f).map_err(|e| {
      key.on_fail(&self.arena);
      e
    })?;

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
          let prev_offset = prev.offset;
          let next_offset = next.offset;
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

          match prev.cas_next_offset_weak(
            &self.arena,
            i,
            next.offset,
            nd.offset,
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
                nd.offset,
                Ordering::SeqCst,
                Ordering::Acquire,
              );

              break;
            }
            Err(_) => {
              // CAS failed. We need to recompute prev and next. It is unlikely to
              // be helpful to try to use a different level as we redo the search,
              // because it is unlikely that lots of nodes are inserted between prev
              // and next.
              let fr = self.find_splice_for_level(trailer.version(), key.as_ref(), i, prev);
              if fr.found {
                if i != 0 {
                  panic!("how can another thread have inserted a node at a non-base level?");
                }

                let node_ptr = fr
                  .curr
                  .expect("the current should not be `None` when we found");
                let old = VersionedEntryRef::from_node(node_ptr, self);

                key.on_fail(&self.arena);

                if upsert {
                  return self.upsert(
                    old, node_ptr, &key, trailer, value_size, f, success, failure,
                  );
                }

                return Ok(Either::Left(if old.is_removed() {
                  None
                } else {
                  Some(old)
                }));
              }

              invalid_data_splice = true;
              prev = fr.splice.prev;
              next = fr.splice.next;
            }
          }
        }
      }
    }

    // Update discard tracker
    unsafe {
      let next = nd.next_offset(&self.arena, 0);
      let ptr = self.arena.get_pointer(next as usize);
      let next_node_ptr = NodePtr::<T>::new(ptr, next);
      let next_node = next_node_ptr.as_ptr();
      let next_node_key = next_node.get_key(&self.arena);
      if self.cmp.compare(next_node_key, key.as_ref()) == cmp::Ordering::Equal {
        self.arena.incr_discard(next_node.size());
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
    self.arena.incr_len();
    self.arena.update_max_version(version);
    self.arena.update_min_version(version);

    Ok(Either::Left(None))
  }

  #[allow(clippy::too_many_arguments)]
  unsafe fn upsert<'a, 'b: 'a, E>(
    &'a self,
    old: VersionedEntryRef<'a, T, C>,
    node_ptr: NodePtr<T>,
    key: &Key<'a, 'b>,
    trailer: T,
    value_size: u32,
    f: impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>,
    success: Ordering,
    failure: Ordering,
  ) -> Result<UpdateOk<'a, 'b, T, C>, Either<E, Error>> {
    match key {
      Key::Occupied(_) | Key::Vacant(_) => node_ptr
        .as_ptr()
        .set_value(&self.arena, trailer, value_size, f)
        .map(|_| Either::Left(if old.is_removed() { None } else { Some(old) })),
      Key::Remove(_) | Key::RemoveVacant(_) => {
        let node = node_ptr.as_ptr();
        let key = node.get_key(&self.arena);
        match node.clear_value(&self.arena, success, failure) {
          Ok((offset, len)) => {
            let trailer = node.get_trailer_by_offset(&self.arena, offset);
            let value = node.get_value_by_offset(&self.arena, offset, len);
            Ok(Either::Right(Ok(VersionedEntryRef {
              map: self,
              key,
              trailer,
              value,
              ptr: node_ptr,
            })))
          }
          Err((offset, len)) => {
            let trailer = node.get_trailer_by_offset(&self.arena, offset);
            let value = node.get_value_by_offset(&self.arena, offset, len);
            Ok(Either::Right(Err(VersionedEntryRef {
              map: self,
              key,
              trailer,
              value,
              ptr: node_ptr,
            })))
          }
        }
      }
    }
  }
}

/// A helper struct for caching splice information
pub struct Inserter<'a, T> {
  spl: [Splice<T>; MAX_HEIGHT],
  height: u32,
  _m: core::marker::PhantomData<&'a ()>,
}

impl<'a, T: Copy> Default for Inserter<'a, T> {
  #[inline]
  fn default() -> Self {
    Self {
      spl: [Splice::default(); MAX_HEIGHT],
      height: 0,
      _m: core::marker::PhantomData,
    }
  }
}

#[derive(Debug, Clone, Copy)]
struct Splice<T> {
  prev: NodePtr<T>,
  next: NodePtr<T>,
}

impl<T> Default for Splice<T> {
  #[inline]
  fn default() -> Self {
    Self {
      prev: NodePtr::NULL,
      next: NodePtr::NULL,
    }
  }
}

struct FindResult<T> {
  found: bool,
  splice: Splice<T>,
  curr: Option<NodePtr<T>>,
}

#[cold]
#[inline(never)]
fn noop<E>(_: &mut VacantBuffer<'_>) -> Result<(), E> {
  Ok(())
}
