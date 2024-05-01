use core::{cmp, ops::RangeBounds};

use crossbeam_utils::CachePadded;

use super::{
  arena::Arena,
  sync::{AtomicU32, Ordering},
  Comparator, MAX_HEIGHT, PROBABILITIES,
};

mod node;
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

/// A fast, cocnurrent map implementation based on skiplist that supports forward
/// and backward iteration. Keys and values are immutable once added to the skipmap and
/// deletion is not supported. Instead, higher-level code is expected to add new
/// entries that shadow existing entries and perform deletion via tombstones. It
/// is up to the user to process these shadow entries and tombstones
/// appropriately during retrieval.
#[derive(Debug)]
pub struct SkipMap<C = ()> {
  arena: Arena,
  head: NodePtr,
  tail: NodePtr,

  /// Current height. 1 <= height <= kMaxHeight. CAS.
  height: CachePadded<AtomicU32>,
  len: CachePadded<AtomicU32>,

  /// If set to true by tests, then extra delays are added to make it easier to
  /// detect unusual race conditions.
  #[cfg(test)]
  testing: bool,

  cmp: C,
}

// Safety: SkipMap is Sync and Send
unsafe impl<C: Comparator> Send for SkipMap<C> {}
unsafe impl<C: Comparator> Sync for SkipMap<C> {}

// --------------------------------Public Methods--------------------------------
impl<C> SkipMap<C> {
  /// Returns the height of the highest tower within any of the nodes that
  /// have ever been allocated as part of this skiplist.
  #[inline]
  pub fn height(&self) -> u32 {
    self.height.load(Ordering::Acquire)
  }

  /// Returns the arena backing this skipmap.
  #[inline]
  pub const fn arena(&self) -> &Arena {
    &self.arena
  }

  /// Returns the comparator used for the skipmap.
  #[inline]
  pub const fn comparator(&self) -> &C {
    &self.cmp
  }

  /// Returns the number of bytes that have allocated from the arena.
  #[inline]
  pub fn size(&self) -> usize {
    self.arena.size()
  }

  /// Returns the number of entries in the skipmap.
  #[inline]
  pub fn len(&self) -> usize {
    self.len.load(Ordering::Acquire) as usize
  }

  /// Returns true if the skipmap is empty.
  #[inline]
  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }
}

impl SkipMap {
  /// Create a new skipmap according to the given capacity
  ///
  /// **Note:** The capacity stands for how many memory allocated,
  /// it does not mean the skiplist can store `cap` entries.
  ///
  ///
  ///
  /// **What the difference between this method and [`SkipMap::mmap_anon`]?**
  ///
  /// 1. This method will use an `AlignedVec` ensures we are working within Rust's memory safety guarantees.
  ///   Even if we are working with raw pointers with `Box::into_raw`,
  ///   the backend ARENA will reclaim the ownership of this memory by converting it back to a `Box`
  ///   when dropping the backend ARENA. Since `AlignedVec` uses heap memory, the data might be more cache-friendly,
  ///   especially if you're frequently accessing or modifying it.
  ///
  /// 2. Where as [`SkipMap::mmap_anon`] will use mmap anonymous to require memory from the OS.
  ///   If you require very large contiguous memory regions, `mmap` might be more suitable because
  ///   it's more direct in requesting large chunks of memory from the OS.
  ///
  /// [`SkipMap::mmap_anon`]: #method.mmap_anon
  pub fn new(cap: usize) -> Result<Self, Error> {
    let arena = Arena::new_vec::<{ Node::MAX_NODE_SIZE }>(cap);
    Self::new_in(arena, ())
  }

  /// Create a new skipmap according to the given capacity, and mmaped to a file.
  ///
  /// **Note:** The capacity stands for how many memory mmaped,
  /// it does not mean the skipmap can store `cap` entries.
  ///
  /// `lock`: whether to lock the underlying file or not
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(not(all(feature = "memmap", target_family = "wasm")))))]
  pub fn mmap(cap: usize, file: std::fs::File, lock: bool) -> std::io::Result<Self> {
    let arena = Arena::new_mmap::<{ Node::MAX_NODE_SIZE }>(cap, file, lock)?;
    Self::new_in(arena, ()).map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))
  }

  /// Create a new skipmap according to the given capacity, and mmap anon.
  ///
  /// **What the difference between this method and [`SkipMap::new`]?**
  ///
  /// 1. This method will use mmap anonymous to require memory from the OS directly.
  ///   If you require very large contiguous memory regions, this method might be more suitable because
  ///   it's more direct in requesting large chunks of memory from the OS.
  ///
  /// 2. Where as [`SkipMap::new`] will use an `AlignedVec` ensures we are working within Rust's memory safety guarantees.
  ///   Even if we are working with raw pointers with `Box::into_raw`,
  ///   the backend ARENA will reclaim the ownership of this memory by converting it back to a `Box`
  ///   when dropping the backend ARENA. Since `AlignedVec` uses heap memory, the data might be more cache-friendly,
  ///   especially if you're frequently accessing or modifying it.
  ///
  /// [`SkipMap::new`]: #method.new
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(not(all(feature = "memmap", target_family = "wasm")))))]
  pub fn mmap_anon(cap: usize) -> std::io::Result<Self> {
    let arena = Arena::new_anonymous_mmap::<{ Node::MAX_NODE_SIZE }>(cap)?;
    Self::new_in(arena, ()).map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))
  }
}

impl<C> SkipMap<C> {
  /// Set comparator for the skipmap.
  pub fn with_comparator<NC: Comparator>(self, cmp: NC) -> SkipMap<NC> {
    SkipMap {
      arena: self.arena,
      head: self.head,
      tail: self.tail,
      height: self.height,
      #[cfg(test)]
      testing: self.testing,
      cmp,
      len: self.len,
    }
  }

  /// Clear the skiplist to empty and re-initialize.
  pub fn clear(&mut self) {
    let head = Node::new_empty_node_ptr(&self.arena)
      .expect("arena is not large enough to hold the head node");
    let tail = Node::new_empty_node_ptr(&self.arena)
      .expect("arena is not large enough to hold the tail node");

    // Safety:
    // We will always allocate enough space for the head node and the tail node.
    unsafe {
      // Link all head/tail levels together.
      for i in 0..MAX_HEIGHT {
        let head_link = head.tower(&self.arena, i);
        let tail_link = tail.tower(&self.arena, i);
        head_link.next_offset.store(tail.offset, Ordering::Relaxed);
        tail_link.prev_offset.store(head.offset, Ordering::Relaxed);
      }
    }

    self.head = head;
    self.tail = tail;
    self.height.store(1, Ordering::Release);
    self.len.store(0, Ordering::Release);
  }
}

impl<C: Comparator> SkipMap<C> {
  /// Returns true if the key exists in the map.
  #[inline]
  pub fn contains_key<'a, 'b: 'a>(&'a self, version: u64, key: &'b [u8]) -> bool {
    self.get(version, key).is_some()
  }

  /// Returns the first entry in the map.
  pub fn first(&self, version: u64) -> Option<EntryRef<'_>> {
    // Safety: head node was definitely allocated by self.arena
    let nd = unsafe { self.get_next(self.head, 0) };
    if nd.is_null() || nd.ptr == self.tail.ptr {
      return None;
    }

    // Safety: we already check the not is not null, and the node is allocated by self.arena
    unsafe {
      let node = nd.as_ptr();
      if node.version > version {
        return None;
      }

      Some(EntryRef {
        key: node.get_key(&self.arena),
        version: node.version,
        value: node.get_value(&self.arena),
      })
    }
  }

  /// Returns the last entry in the map.
  pub fn last(&self, version: u64) -> Option<EntryRef<'_>> {
    // Safety: tail node was definitely allocated by self.arena
    let mut nd = unsafe { self.get_prev(self.tail, 0) };

    loop {
      if nd.is_null() || nd.ptr == self.head.ptr {
        return None;
      }

      // Safety: we already check the node is not null, and the node is allocated by self.arena
      unsafe {
        let node = nd.as_ptr();
        if node.version <= version {
          return Some(EntryRef {
            key: node.get_key(&self.arena),
            version: node.version,
            value: node.get_value(&self.arena),
          });
        }
        nd = self.get_prev(nd, 0);
      }
    }
  }

  /// Returns the value associated with the given key, if it exists.
  pub fn get<'a, 'b: 'a>(&'a self, version: u64, key: &'b [u8]) -> Option<EntryRef<'a>> {
    self.get_in(version, key).and_then(|ptr| unsafe {
      if ptr.is_null() {
        return None;
      }

      let node = ptr.as_ptr();
      Some(EntryRef {
        key: node.get_key(&self.arena),
        version: node.version,
        value: node.get_value(&self.arena),
      })
    })
  }

  /// Returns the entry greater or equal to the given key, if it exists.
  ///
  /// e.g.
  ///
  /// - If k1 < k2 < k3, key is equal to k1, then the entry contains k2 will be returned.
  /// - If k1 < k2 < k3, and k1 < key < k2, then the entry contains k2 will be returned.
  pub fn gt<'a, 'b: 'a>(&'a self, version: u64, key: &'b [u8]) -> Option<EntryRef<'a>> {
    self.gt_in(version, key).map(|ptr| unsafe {
      // Safety: the gt_in guarantees that ptr is valid,
      let node = ptr.as_ptr();
      EntryRef {
        key: node.get_key(&self.arena),
        version: node.version,
        value: node.get_value(&self.arena),
      }
    })
  }

  /// Returns the entry less than the given key, if it exists.
  ///
  /// e.g.
  ///
  /// - If k1 < k2 < k3, and key is equal to k3, then the entry contains k2 will be returned.
  /// - If k1 < k2 < k3, and k2 < key < k3, then the entry contains k2 will be returned.
  pub fn lt<'a, 'b: 'a>(&'a self, version: u64, key: &'b [u8]) -> Option<EntryRef<'a>> {
    self.lt_in(version, key).map(|ptr| unsafe {
      // Safety: the lt_in guarantees that ptr is valid,
      let node = ptr.as_ptr();
      EntryRef {
        key: node.get_key(&self.arena),
        version: node.version,
        value: node.get_value(&self.arena),
      }
    })
  }

  /// Returns the entry greater than or equal to the given key, if it exists.
  ///
  /// e.g.
  ///
  /// - If k1 < k2 < k3, key is equal to k1, then the entry contains k1 will be returned.
  /// - If k1 < k2 < k3, and k1 < key < k2, then the entry contains k2 will be returned.
  pub fn ge<'a, 'b: 'a>(&'a self, version: u64, key: &'b [u8]) -> Option<EntryRef<'a>> {
    self.ge_in(version, key).map(|ptr| unsafe {
      // Safety: the ge_in guarantees that ptr is valid,
      let node = ptr.as_ptr();
      EntryRef {
        key: node.get_key(&self.arena),
        version: node.version,
        value: node.get_value(&self.arena),
      }
    })
  }

  /// Returns the entry less than or equal to the given key, if it exists.
  ///
  /// e.g.
  ///
  /// - If k1 < k2 < k3, and key is equal to k3, then the entry contains k3 will be returned.
  /// - If k1 < k2 < k3, and k2 < key < k3, then the entry contains k2 will be returned.
  pub fn le<'a, 'b: 'a>(&'a self, version: u64, key: &'b [u8]) -> Option<EntryRef<'a>> {
    self.le_in(version, key).map(|ptr| unsafe {
      // Safety: the le_in guarantees that ptr is valid,
      let node = ptr.as_ptr();
      EntryRef {
        key: node.get_key(&self.arena),
        version: node.version,
        value: node.get_value(&self.arena),
      }
    })
  }

  /// Gets or inserts a new entry.
  ///
  /// # Success
  ///
  /// - Returns `Ok(Some(&[u8]))` if the key exists.
  /// - Returns `Ok(None)` if the key does not exist, and successfully inserts the key and value.
  ///
  /// As a low-level crate, users are expected to handle the error cases themselves.
  ///
  /// # Errors
  ///
  /// - Returns `Err(Error::Duplicated)`, if the key already exists.
  /// - Returns `Err(Error::Full)`, if there isn't enough room in the arena.
  pub fn get_or_insert<'a, 'b: 'a>(
    &'a self,
    version: u64,
    key: &'b [u8],
    value: &'b [u8],
  ) -> Result<Option<EntryRef<'a>>, Error> {
    let ins = &mut Default::default();

    unsafe {
      let (_, curr) = self.find_splice(version, key, ins, true);
      if let Some(curr) = curr {
        if curr.is_null() {
          return self.insert_in(version, key, value, ins).map(|_| None);
        }

        return Ok(Some({
          let nd = curr.as_ptr();
          EntryRef {
            key: nd.get_key(&self.arena),
            version: nd.version,
            value: nd.get_value(&self.arena),
          }
        }));
      }
      self.insert_in(version, key, value, ins).map(|_| None)
    }
  }

  /// Inserts a new key if it does not yet exist. Returns `Ok(())` if the key was successfully inserted.
  ///
  /// As a low-level crate, users are expected to handle the error cases themselves.
  ///
  /// # Errors
  ///
  /// - Returns `Error::Duplicated`, if the key already exists.
  /// - Returns `Error::Full`, if there isn't enough room in the arena.
  pub fn insert<'a, 'b: 'a>(
    &'a self,
    version: u64,
    key: &'b [u8],
    value: &'b [u8],
  ) -> Result<(), Error> {
    self.insert_in(version, key, value, &mut Inserter::default())
  }

  /// Returns a new `Iterator`. Note that it is
  /// safe for an iterator to be copied by value.
  #[inline]
  pub const fn iter(&self, version: u64) -> iterator::MapIterator<C> {
    iterator::MapIterator::new(version, self)
  }

  /// Returns a `Iterator` that within the range.
  #[inline]
  pub fn range<'a, Q, R>(&'a self, version: u64, range: R) -> iterator::MapRange<'a, C, Q, R>
  where
    &'a [u8]: PartialOrd<Q>,
    Q: ?Sized + PartialOrd<&'a [u8]>,
    R: RangeBounds<Q> + 'a,
  {
    iterator::MapIterator::range(version, self, range)
  }
}

// --------------------------------Crate Level Methods--------------------------------
impl<C: Comparator> SkipMap<C> {
  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[inline]
  pub(crate) unsafe fn get_prev(&self, nd: NodePtr, height: usize) -> NodePtr {
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
  pub(crate) unsafe fn get_next(&self, nptr: NodePtr, height: usize) -> NodePtr {
    if nptr.is_null() {
      return NodePtr::NULL;
    }
    let offset = nptr.next_offset(&self.arena, height);
    let ptr = self.arena.get_pointer(offset as usize);
    NodePtr::new(ptr, offset)
  }
}

// --------------------------------Private Methods--------------------------------
impl<C> SkipMap<C> {
  fn new_in(arena: Arena, cmp: C) -> Result<Self, Error> {
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

    Ok(Self {
      arena,
      head,
      tail,
      height: CachePadded::new(AtomicU32::new(1)),
      #[cfg(test)]
      testing: false,
      cmp,
      len: CachePadded::new(AtomicU32::new(0)),
    })
  }

  #[allow(clippy::type_complexity)]
  fn new_node(&self, key: &[u8], version: u64, value: &[u8]) -> Result<(NodePtr, u32), Error> {
    let height = Self::random_height();
    let nd = Node::new_node_ptr(&self.arena, height, key, version, value)?;

    // Try to increase self.height via CAS.
    let mut list_height = self.height();
    while height > list_height {
      match self.height.compare_exchange_weak(
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

  #[cfg(feature = "std")]
  #[inline]
  fn random_height() -> u32 {
    use rand::{thread_rng, Rng};
    let mut rng = thread_rng();
    let rnd: u32 = rng.gen();
    let mut h = 1;

    while h < MAX_HEIGHT && rnd <= PROBABILITIES[h] {
      h += 1;
    }
    h as u32
  }

  #[cfg(not(feature = "std"))]
  #[inline]
  fn random_height() -> u32 {
    use rand::{rngs::OsRng, Rng, RngCore};

    let rnd: u32 = OsRng.gen();
    let mut h = 1;

    while h < MAX_HEIGHT && rnd <= PROBABILITIES[h] {
      h += 1;
    }
    h as u32
  }
}

impl<C: Comparator> SkipMap<C> {
  fn get_in(&self, version: u64, key: &[u8]) -> Option<NodePtr> {
    let mut lvl = (self.height() - 1) as usize;

    let mut prev = self.head;
    loop {
      let fr = unsafe { self.find_splice_for_level(version, key, lvl, prev) };
      if fr.found {
        return fr.curr;
      }
      if lvl == 0 {
        break;
      }

      prev = fr.splice.prev;
      lvl -= 1;
    }

    None
  }

  fn lt_in(&self, version: u64, key: &[u8]) -> Option<NodePtr> {
    let res = self.seek_for_base_splice(version, key);
    let nd = res.prev;
    if nd.is_null() || nd.ptr == self.head.ptr {
      return None;
    }
    Some(nd)
  }

  fn gt_in(&self, version: u64, key: &[u8]) -> Option<NodePtr> {
    let res = self.seek_for_base_splice(version, key);
    let mut nd = res.next;
    if nd.is_null() || nd.ptr == self.tail.ptr {
      return None;
    }

    unsafe {
      let node = nd.as_ptr();
      if self.cmp.compare(key, node.get_key(&self.arena)) == cmp::Ordering::Equal
        && self.cmp.compare_version(node.version, version) == cmp::Ordering::Equal
      {
        nd = self.get_next(nd, 0);
        if nd.ptr == self.tail.ptr {
          return None;
        }
      }
    }
    Some(nd)
  }

  fn le_in(&self, version: u64, key: &[u8]) -> Option<NodePtr> {
    let res = self.seek_for_base_splice(version, key);
    let mut nd = res.prev;
    if nd.is_null() || nd.ptr == self.head.ptr {
      return None;
    }

    unsafe {
      let node = res.next.as_ptr();

      if self.cmp.compare(key, node.get_key(&self.arena)) == cmp::Ordering::Equal
        && self.cmp.compare_version(node.version, version) == cmp::Ordering::Equal
      {
        nd = res.next;
      }

      if nd.ptr == self.head.ptr {
        return None;
      }
    }
    Some(nd)
  }

  fn ge_in(&self, version: u64, key: &[u8]) -> Option<NodePtr> {
    let res = self.seek_for_base_splice(version, key);
    let nd = res.next;
    if nd.is_null() || nd.ptr == self.tail.ptr {
      return None;
    }

    Some(nd)
  }

  fn insert_in(
    &self,
    version: u64,
    key: &[u8],
    value: &[u8],
    ins: &mut Inserter,
  ) -> Result<(), Error> {
    // Safety: a fresh new Inserter, so safe here
    if unsafe { self.find_splice(version, key, ins, false).0 } {
      return Err(Error::Duplicated);
    }

    #[cfg(all(test, feature = "std"))]
    if self.testing {
      // Add delay to make it easier to test race between this thread
      // and another thread that sees the intermediate state between
      // finding the splice and using it.
      std::thread::yield_now();
    }

    let (nd, height) = self.new_node(key, version, value)?;
    // We always insert from the base level and up. After you add a node in base
    // level, we cannot create a node in the level above because it would have
    // discovered the node in the base level.
    let mut invalid_date_splice = false;

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
              let link = next.tower(&self.arena, i);
              let _ = link.prev_offset.compare_exchange(
                next_prev_offset,
                prev_offset,
                Ordering::SeqCst,
                Ordering::Acquire,
              );
            }
          }

          let prev_link = prev.tower(&self.arena, i);
          match prev_link.next_offset.compare_exchange_weak(
            next.offset,
            nd.offset,
            Ordering::SeqCst,
            Ordering::Acquire,
          ) {
            Ok(_) => {
              // Managed to insert nd between prev and next, so update the next
              // node's prev link and go to the next level.
              #[cfg(all(test, feature = "std"))]
              if self.testing {
                // Add delay to make it easier to test race between this thread
                // and another thread that sees the intermediate state between
                // setting next and setting prev.
                std::thread::yield_now();
              }

              let next_link = next.tower(&self.arena, i);
              let _ = next_link.prev_offset.compare_exchange(
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
              let fr = self.find_splice_for_level(version, key, i, prev);
              if fr.found {
                if i != 0 {
                  panic!("how can another thread have inserted a node at a non-base level?");
                }

                return Err(Error::Duplicated);
              }

              invalid_date_splice = true;
              prev = fr.splice.prev;
              next = fr.splice.next;
            }
          }
        }
      }
    }

    // If we had to recompute the splice for a level, invalidate the entire
    // cached splice.
    if invalid_date_splice {
      ins.height = 0;
    } else {
      // The splice was valid. We inserted a node between spl[i].prev and
      // spl[i].next. Optimistically update spl[i].prev for use in a subsequent
      // call to add.
      for i in 0..(height as usize) {
        ins.spl[i].prev = nd;
      }
    }
    self.len.fetch_add(1, Ordering::AcqRel);
    Ok(())
  }

  /// ## Safety:
  /// - All of splices in the inserter must be contains node ptrs are allocated by the current skip map.
  unsafe fn find_splice(
    &self,
    version: u64,
    key: &[u8],
    ins: &mut Inserter,
    returned_when_found: bool,
  ) -> (bool, Option<NodePtr>) {
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
    start: NodePtr,
  ) -> FindResult {
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

      let (key_offset, key_size) = (next_node.key_offset, next_node.key_size);
      let next_key = self.arena.get_bytes(key_offset as usize, key_size as usize);

      match self.cmp.compare(key, next_key) {
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
          // User-key equality.
          let cmp = self.cmp.compare_version(version, next_node.version);

          if let cmp::Ordering::Equal = cmp {
            // Internal key equality.
            return FindResult {
              splice: Splice { prev, next },
              found: true,
              curr: Some(next),
            };
          }

          if let cmp::Ordering::Greater = cmp {
            // We are done for this level, since prev.key < key < next.key.
            return FindResult {
              splice: Splice { prev, next },
              found: false,
              curr: None,
            };
          }

          // Keep moving right on this level.
          prev = next;
        }
      }
    }
  }

  /// ## Safety
  /// - The caller must ensure that the node is allocated by the arena.
  /// - The caller must ensure that the node is not null.
  unsafe fn key_is_after_node(&self, nd: NodePtr, version: u64, key: &[u8]) -> bool {
    let nd = &*nd.ptr;
    let nd_key = self
      .arena
      .get_bytes(nd.key_offset as usize, nd.key_size as usize);

    match self.cmp.compare(nd_key, key) {
      cmp::Ordering::Less => true,
      cmp::Ordering::Greater => false,
      cmp::Ordering::Equal => {
        // User-key equality.
        let cmp = self.cmp.compare_version(nd.version, version);
        if cmp == cmp::Ordering::Equal {
          // Trailer equality.
          return false;
        }
        cmp == cmp::Ordering::Less
      }
    }
  }

  fn seek_for_base_splice(&self, version: u64, key: &[u8]) -> SeekResult {
    let mut lvl = (self.height() - 1) as usize;

    let mut prev = self.head;
    let mut next;

    loop {
      let fr = unsafe { self.find_splice_for_level(version, key, lvl, prev) };
      prev = fr.splice.prev;
      next = fr.splice.next;
      if fr.found {
        if lvl != 0 {
          // next is pointing at the target node, but we need to find previous on
          // the bottom level.

          // Safety: the next we use here is got from the find_splice_for_level, so must be allocated by the same arena
          prev = unsafe { self.get_prev(next, 0) };
        }
        break;
      }

      if lvl == 0 {
        break;
      }

      lvl -= 1;
    }

    SeekResult { prev, next }
  }
}

/// A helper struct for caching splice information
pub struct Inserter<'a> {
  spl: [Splice; MAX_HEIGHT],
  height: u32,
  _m: core::marker::PhantomData<&'a ()>,
}

impl<'a> Default for Inserter<'a> {
  #[inline]
  fn default() -> Self {
    Self {
      spl: [Splice::default(); MAX_HEIGHT],
      height: 0,
      _m: core::marker::PhantomData,
    }
  }
}

struct Splice {
  prev: NodePtr,
  next: NodePtr,
}

impl Default for Splice {
  #[inline]
  fn default() -> Self {
    Self {
      prev: NodePtr::NULL,
      next: NodePtr::NULL,
    }
  }
}

impl Clone for Splice {
  #[inline]
  fn clone(&self) -> Self {
    *self
  }
}

impl Copy for Splice {}

struct FindResult {
  found: bool,
  splice: Splice,
  curr: Option<NodePtr>,
}

struct SeekResult {
  prev: NodePtr,
  next: NodePtr,
}
