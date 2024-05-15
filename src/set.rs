use core::{
  cmp,
  ops::{Bound, RangeBounds},
};

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
use super::{MmapOptions, OpenOptions};
use crate::Trailer;

use super::{arena::Arena, sync::Ordering, Ascend, Comparator, MAX_HEIGHT};

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

// #[cfg(all(test, loom))]
// mod loom;

/// A fast, cocnurrent map implementation based on skiplist that supports forward
/// and backward iteration. Keys and values are immutable once added to the skipset and
/// deletion is not supported. Instead, higher-level code is expected to add new
/// entries that shadow existing entries and perform deletion via tombstones. It
/// is up to the user to process these shadow entries and tombstones
/// appropriately during retrieval.
#[derive(Debug)]
pub struct SkipSet<T = u64, C = Ascend> {
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

// Safety: SkipSet is Sync and Send
unsafe impl<T: Send, C: Comparator + Send> Send for SkipSet<T, C> {}
unsafe impl<T: Send, C: Comparator + Sync> Sync for SkipSet<T, C> {}

// --------------------------------Public Methods--------------------------------
impl<T, C: Clone> Clone for SkipSet<T, C> {
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

impl<T, C> SkipSet<T, C> {
  /// Returns the height of the highest tower within any of the nodes that
  /// have ever been allocated as part of this skiplist.
  #[inline]
  pub fn height(&self) -> u32 {
    self.arena.height()
  }

  /// Returns the number of bytes that have allocated from the arena.
  #[inline]
  pub fn size(&self) -> usize {
    self.arena.size()
  }

  /// Returns the capacity of the arena.
  #[inline]
  pub const fn capacity(&self) -> usize {
    self.arena.capacity()
  }

  /// Returns the number of remaining bytes can be allocated by the arena.
  #[inline]
  pub fn remaining(&self) -> usize {
    self.arena.remaining()
  }

  /// Returns the number of entries in the skipset.
  #[inline]
  pub fn len(&self) -> usize {
    self.arena.len() as usize
  }

  /// Returns true if the skipset is empty.
  #[inline]
  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }

  /// Returns the comparator used to compare keys.
  #[inline]
  pub const fn comparator(&self) -> &C {
    &self.cmp
  }

  /// Returns the maximum version of all entries in the set.
  #[inline]
  pub fn max_version(&self) -> u64 {
    self.arena.max_version()
  }

  /// Returns the minimum version of all entries in the set.
  #[inline]
  pub fn min_version(&self) -> u64 {
    self.arena.min_version()
  }

  /// Flushes outstanding memory map modifications to disk.
  ///
  /// When this method returns with a non-error result,
  /// all outstanding changes to a file-backed memory map are guaranteed to be durably stored.
  /// The file's metadata (including last modification timestamp) may not be updated.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn flush(&self) -> std::io::Result<()> {
    self.arena.flush()
  }

  /// Asynchronously flushes outstanding memory map modifications to disk.
  ///
  /// This method initiates flushing modified pages to durable storage, but it will not wait for
  /// the operation to complete before returning. The file's metadata (including last
  /// modification timestamp) may not be updated.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn flush_async(&self) -> std::io::Result<()> {
    self.arena.flush_async()
  }

  #[cfg(all(test, feature = "std"))]
  #[inline]
  pub(crate) fn with_yield_now(mut self) -> Self {
    self.yield_now = true;
    self
  }
}

impl SkipSet {
  /// Create a new skipset according to the given capacity
  ///
  /// **Note:** The capacity stands for how many memory allocated,
  /// it does not mean the skiplist can store `cap` entries.
  ///
  ///
  ///
  /// **What the difference between this method and [`SkipSet::mmap_anon`]?**
  ///
  /// 1. This method will use an `AlignedVec` ensures we are working within Rust's memory safety guarantees.
  ///   Even if we are working with raw pointers with `Box::into_raw`,
  ///   the backend ARENA will reclaim the ownership of this memory by converting it back to a `Box`
  ///   when dropping the backend ARENA. Since `AlignedVec` uses heap memory, the data might be more cache-friendly,
  ///   especially if you're frequently accessing or modifying it.
  ///
  /// 2. Where as [`SkipSet::mmap_anon`] will use mmap anonymous to require memory from the OS.
  ///   If you require very large contiguous memory regions, `mmap` might be more suitable because
  ///   it's more direct in requesting large chunks of memory from the OS.
  ///
  /// [`SkipSet::mmap_anon`]: #method.mmap_anon
  pub fn new(cap: usize) -> Result<Self, Error> {
    Self::with_comparator(cap, Ascend)
  }

  /// Create a new skipset according to the given capacity, and mmaped to a file.
  ///
  /// **Note:** The capacity stands for how many memory mmaped,
  /// it does not mean the skipset can store `cap` entries.
  ///
  /// `lock`: whether to lock the underlying file or not
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn mmap_mut<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> std::io::Result<Self> {
    Self::mmap_mut_with_comparator(path, open_options, mmap_options, Ascend)
  }

  /// Open an exist file and mmap it to create skipset.
  ///
  /// `lock`: whether to lock the underlying file or not
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn mmap<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> std::io::Result<Self> {
    Self::mmap_with_comparator(path, open_options, mmap_options, Ascend)
  }

  /// Create a new skipset according to the given capacity, and mmap anon.
  ///
  /// **What the difference between this method and [`SkipSet::new`]?**
  ///
  /// 1. This method will use mmap anonymous to require memory from the OS directly.
  ///   If you require very large contiguous memory regions, this method might be more suitable because
  ///   it's more direct in requesting large chunks of memory from the OS.
  ///
  /// 2. Where as [`SkipSet::new`] will use an `AlignedVec` ensures we are working within Rust's memory safety guarantees.
  ///   Even if we are working with raw pointers with `Box::into_raw`,
  ///   the backend ARENA will reclaim the ownership of this memory by converting it back to a `Box`
  ///   when dropping the backend ARENA. Since `AlignedVec` uses heap memory, the data might be more cache-friendly,
  ///   especially if you're frequently accessing or modifying it.
  ///
  /// [`SkipSet::new`]: #method.new
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn mmap_anon(opts: MmapOptions) -> std::io::Result<Self> {
    Self::mmap_anon_with_comparator(opts, Ascend)
  }
}

impl<T, C> SkipSet<T, C> {
  /// Like [`SkipSet::new`], but with a custom comparator.
  pub fn with_comparator(cap: usize, cmp: C) -> Result<Self, Error> {
    let arena = Arena::new_vec(cap, Node::<T>::min_cap(), Node::<T>::alignment() as usize);
    Self::new_in(arena, cmp, false)
  }

  /// Like [`SkipSet::mmap_mut`], but with a custom comparator.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn mmap_mut_with_comparator<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    cmp: C,
  ) -> std::io::Result<Self> {
    let arena = Arena::mmap_mut(
      path,
      open_options,
      mmap_options,
      Node::<T>::min_cap(),
      Node::<T>::alignment() as usize,
    )?;
    Self::new_in(arena, cmp, false)
      .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))
  }

  /// Like [`SkipSet::mmap`], but with a custom comparator.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn mmap_with_comparator<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    cmp: C,
  ) -> std::io::Result<Self> {
    let arena = Arena::mmap(
      path,
      open_options,
      mmap_options,
      Node::<T>::min_cap(),
      Node::<T>::alignment() as usize,
    )?;
    Self::new_in(arena, cmp, true)
      .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))
  }

  /// Like [`SkipSet::mmap_anon`], but with a custom comparator.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn mmap_anon_with_comparator(opts: MmapOptions, cmp: C) -> std::io::Result<Self> {
    let arena =
      Arena::new_anonymous_mmap(opts, Node::<T>::min_cap(), Node::<T>::alignment() as usize)?;
    Self::new_in(arena, cmp, false)
      .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))
  }

  /// Clear the skiplist to empty and re-initialize.
  ///
  /// # Safety
  /// This mehod is not concurrency safe, invokers must ensure that no other threads are accessing the skipset.
  pub unsafe fn clear(&mut self) {
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
    self.arena.clear();
  }

  fn new_in(arena: Arena, cmp: C, ro: bool) -> Result<Self, Error> {
    if ro {
      let (ptr, offset) = arena.head_ptr(Node::<T>::MAX_NODE_SIZE as u32, Node::<T>::alignment());
      let head = NodePtr::new(ptr, offset);
      let (ptr, offset) = arena.tail_ptr(Node::<T>::MAX_NODE_SIZE as u32, Node::<T>::alignment());
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

impl<T: Trailer, C: Comparator> SkipSet<T, C> {
  /// Returns true if the key exists in the map.
  #[inline]
  pub fn contains_key<'a, 'b: 'a>(&'a self, version: u64, key: &'b [u8]) -> bool {
    self.get(version, key).is_some()
  }

  /// Returns the first entry in the map.
  pub fn first(&self, version: u64) -> Option<EntryRef<'_, T, C>> {
    self.first_in(version).map(|n| EntryRef::from_node(n, self))
  }

  /// Returns the last entry in the map.
  pub fn last(&self, version: u64) -> Option<EntryRef<'_, T, C>> {
    self.last_in(version).map(|n| EntryRef::from_node(n, self))
  }

  /// Returns the value associated with the given key, if it exists.
  pub fn get<'a, 'b: 'a>(&'a self, version: u64, key: &'b [u8]) -> Option<EntryRef<'a, T, C>> {
    unsafe {
      let (n, eq) = self.find_near(version, key, false, true); // findLessOrEqual.

      let n = n?;
      let node = n.as_ptr();
      let node_key = node.get_key(&self.arena);

      if eq {
        return Some(EntryRef {
          set: self,
          key: node_key,
          trailer: node.trailer,
        });
      }

      if !matches!(self.cmp.compare(key, node_key), cmp::Ordering::Equal) {
        return None;
      }

      if node.trailer.version() > version {
        return None;
      }

      Some(EntryRef {
        set: self,
        key: node_key,
        trailer: node.trailer,
      })
    }
  }

  /// Returns an `EntryRef` pointing to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  pub fn upper_bound<'a, 'b: 'a>(
    &'a self,
    version: u64,
    upper: Bound<&'b [u8]>,
  ) -> Option<EntryRef<'a, T, C>> {
    match upper {
      Bound::Included(key) => self.le(version, key).map(|n| EntryRef::from_node(n, self)),
      Bound::Excluded(key) => self.lt(version, key).map(|n| EntryRef::from_node(n, self)),
      Bound::Unbounded => self.last(version),
    }
  }

  /// Returns an `EntryRef` pointing to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  pub fn lower_bound<'a, 'b: 'a>(
    &'a self,
    version: u64,
    lower: Bound<&'b [u8]>,
  ) -> Option<EntryRef<'a, T, C>> {
    match lower {
      Bound::Included(key) => self.ge(version, key).map(|n| EntryRef::from_node(n, self)),
      Bound::Excluded(key) => self.gt(version, key).map(|n| EntryRef::from_node(n, self)),
      Bound::Unbounded => self.first(version),
    }
  }

  /// Inserts a new key if it does not yet exist. Returns `Ok(())` if the key was successfully inserted.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(_))` if the key with the same trailer already exists.
  pub fn insert<'a, 'b: 'a>(
    &'a self,
    trailer: T,
    key: &'b [u8],
  ) -> Result<Option<EntryRef<'a, T, C>>, Error> {
    if self.ro {
      return Err(Error::Readonly);
    }

    self.insert_in(trailer, key, &mut Inserter::default())
  }

  /// Returns a new iterator, this iterator will yield the latest version of all entries in the map less or equal to the given version.
  #[inline]
  pub const fn iter(&self, version: u64) -> iterator::SetIterator<T, C> {
    iterator::SetIterator::new(version, self, false)
  }

  /// Returns a new iterator, this iterator will yield all versions for all entries in the map less or equal to the given version.
  #[inline]
  pub const fn iter_all_versions(&self, version: u64) -> iterator::SetIterator<T, C> {
    iterator::SetIterator::new(version, self, true)
  }

  /// Returns a iterator that within the range, this iterator will yield the latest version of all entries in the range less or equal to the given version.
  #[inline]
  pub fn range<'a, Q, R>(&'a self, version: u64, range: R) -> iterator::SetIterator<'a, T, C, Q, R>
  where
    &'a [u8]: PartialOrd<Q>,
    Q: ?Sized + PartialOrd<&'a [u8]>,
    R: RangeBounds<Q> + 'a,
  {
    iterator::SetIterator::range(version, self, range, false)
  }

  /// Returns a iterator that within the range, this iterator will yield all versions for all entries in the range less or equal to the given version.
  #[inline]
  pub fn range_all_versions<'a, Q, R>(
    &'a self,
    version: u64,
    range: R,
  ) -> iterator::SetIterator<'a, T, C, Q, R>
  where
    &'a [u8]: PartialOrd<Q>,
    Q: ?Sized + PartialOrd<&'a [u8]>,
    R: RangeBounds<Q> + 'a,
  {
    iterator::SetIterator::range(version, self, range, true)
  }
}

// --------------------------------Crate Level Methods--------------------------------
impl<T: Trailer, C: Comparator> SkipSet<T, C> {
  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[inline]
  pub(crate) unsafe fn get_prev(&self, nd: NodePtr<T>, height: usize) -> NodePtr<T> {
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
  pub(crate) unsafe fn get_next(&self, nptr: NodePtr<T>, height: usize) -> NodePtr<T> {
    if nptr.is_null() {
      return NodePtr::NULL;
    }
    let offset = nptr.next_offset(&self.arena, height);
    let ptr = self.arena.get_pointer(offset as usize);
    NodePtr::new(ptr, offset)
  }
}

// --------------------------------Private Methods--------------------------------
impl<T: Trailer, C> SkipSet<T, C> {
  #[allow(clippy::type_complexity)]
  fn new_node(&self, key: &[u8], trailer: T) -> Result<(NodePtr<T>, u32), Error> {
    let height = super::random_height();
    let nd = Node::new_node_ptr(&self.arena, height, key, trailer)?;

    // Try to increase self.height via CAS.
    let mut list_height = self.height();
    while height > list_height {
      match self.arena.atomic_height().compare_exchange_weak(
        list_height,
        height,
        Ordering::SeqCst,
        Ordering::Acquire,
      ) {
        // Successfully increased skiplist.arena.height.
        Ok(_) => break,
        Err(h) => list_height = h,
      }
    }
    Ok((nd, height))
  }
}

impl<T: Trailer, C: Comparator> SkipSet<T, C> {
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

  fn insert_in(
    &self,
    trailer: T,
    key: &[u8],
    ins: &mut Inserter<T>,
  ) -> Result<Option<EntryRef<'_, T, C>>, Error> {
    let version = trailer.version();

    // Safety: a fresh new Inserter, so safe here
    unsafe {
      let (found, ptr) = self.find_splice(trailer.version(), key, ins, true);
      if found {
        return Ok(Some(EntryRef::from_node(
          ptr.expect("the NodePtr cannot be `None` when we found"),
          self,
        )));
      }
    }

    #[cfg(all(test, feature = "std"))]
    if self.yield_now {
      // Add delay to make it easier to test race between this thread
      // and another thread that sees the intermediate state between
      // finding the splice and using it.
      std::thread::yield_now();
    }

    let (nd, height) = self.new_node(key, trailer)?;
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
              if self.yield_now {
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
              let fr = self.find_splice_for_level(trailer.version(), key, i, prev);
              if fr.found {
                if i != 0 {
                  panic!("how can another thread have inserted a node at a non-base level?");
                }

                return Ok(Some(EntryRef::from_node(
                  fr.curr
                    .expect("the current should not be `None` when we found"),
                  self,
                )));
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
    self.arena.incr_len();
    self.arena.update_max_version(version);
    self.arena.update_min_version(version);
    Ok(None)
  }

  unsafe fn find_prev_max_version(&self, mut curr: NodePtr<T>, version: u64) -> Option<NodePtr<T>> {
    let mut prev = self.get_prev(curr, 0);

    loop {
      let curr_node = curr.as_ptr();
      let curr_key = curr_node.get_key(&self.arena);
      // if the current version is greater than the given version, we should return.
      let version_cmp = curr_node.trailer.version().cmp(&version);
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

      let version_cmp = prev_node.trailer.version().cmp(&version);

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
      let version_cmp = curr_node.trailer.version().cmp(&version);
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
      let version_cmp = next_node.trailer.version().cmp(&version);
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
        .then_with(|| next_node.trailer.version().cmp(&version));

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
  unsafe fn find_splice(
    &self,
    version: u64,
    key: &[u8],
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

      let (key_offset, key_size) = (next_node.key_offset, next_node.key_size);
      let next_key = self.arena.get_bytes(key_offset as usize, key_size as usize);

      match self
        .cmp
        .compare(key, next_key)
        .then_with(|| next_node.trailer.version().cmp(&version))
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
        matches!(version.cmp(&nd.trailer.version()), cmp::Ordering::Less)
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
      spl: [Splice::<T>::default(); MAX_HEIGHT],
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
