use core::borrow::Borrow;

use super::*;

use base::{AllVersionsIter, EntryRef, Iter};

type Allocator = GenericAllocator<Meta, RawNode, Arena>;
type SkipList<C> = base::SkipList<Allocator, C>;

node_pointer!(RawNode);

/// A raw node that does not support version and trailer.
#[repr(C)]
pub struct RawNode {
  // A byte slice is 24 bytes. We are trying to save space here.
  /// Multiple parts of the value are encoded as a single u64 so that it
  /// can be atomically loaded and stored:
  ///   value offset: u32 (bits 0-31)
  ///   value size  : u32 (bits 32-63)
  value: UnsyncValuePointer,
  // Immutable. No need to lock to access key.
  key_offset: u32,
  // Immutable. No need to lock to access key.
  key_size_and_height: u32,
  // ** DO NOT REMOVE BELOW COMMENT**
  // The below field will be attached after the node, have to comment out
  // this field, because each node will not use the full height, the code will
  // not allocate the full size of the tower.
  //
  // Most nodes do not need to use the full height of the tower, since the
  // probability of each successive level decreases exponentially. Because
  // these elements are never accessed, they do not need to be allocated.
  // Therefore, when a node is allocated in the arena, its memory footprint
  // is deliberately truncated to not include unneeded tower elements.
  //
  // All accesses to elements should use CAS operations, with no need to lock.
  // pub(super) tower: [Link; self.opts.max_height],
}

impl core::fmt::Debug for RawNode {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    let (key_size, height) = decode_key_size_and_height(self.key_size_and_height);
    let (value_offset, value_size) = self.value.load();
    f.debug_struct("Node")
      .field("value_offset", &value_offset)
      .field("value_size", &value_size)
      .field("key_offset", &self.key_offset)
      .field("key_size", &key_size)
      .field("height", &height)
      .finish()
  }
}

impl Node for RawNode {
  type Link = Link;

  type Trailer = ();

  type ValuePointer = UnsyncValuePointer;

  type Pointer = NodePointer;

  fn full(value_offset: u32, max_height: u8) -> Self {
    Self {
      value: UnsyncValuePointer::new(value_offset, 0),
      key_offset: 0,
      key_size_and_height: encode_key_size_and_height(0, max_height),
    }
  }

  #[inline]
  fn value_pointer(&self) -> &Self::ValuePointer {
    &self.value
  }

  #[inline]
  fn set_value_pointer(&mut self, offset: u32, size: u32) {
    self.value = UnsyncValuePointer::new(offset, size);
  }

  #[inline]
  fn clear_value<A: super::Allocator>(
    &self,
    arena: &A,
    success: Ordering,
    failure: Ordering,
  ) -> Result<(), (u32, u32)> {
    self
      .value
      .compare_remove(success, failure)
      .map(|(_, old_len)| {
        if old_len != REMOVE {
          arena.increase_discarded(old_len);
        }
      })
  }

  #[inline]
  fn set_key_size_and_height(&mut self, key_size_and_height: u32) {
    self.key_size_and_height = key_size_and_height;
  }

  #[inline]
  fn set_key_offset(&mut self, key_offset: u32) {
    self.key_offset = key_offset;
  }

  #[inline]
  fn version(&self) -> Version {
    0
  }

  #[inline]
  fn set_version(&mut self, _: Version) {}

  #[inline]
  fn key_size_and_height(&self) -> u32 {
    self.key_size_and_height
  }

  #[inline]
  fn key_offset(&self) -> u32 {
    self.key_offset
  }
}

/// A fast, cocnurrent map implementation based on skiplist that supports forward
/// and backward iteration.
#[repr(transparent)]
pub struct SkipMap<C = Ascend>(SkipList<C>);

impl<C: Clone> Clone for SkipMap<C> {
  #[inline]
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl SkipMap {
  /// Create a new skipmap with default options.
  ///
  /// **Note:** The capacity stands for how many memory allocated,
  /// it does not mean the skiplist can store `cap` entries.
  ///
  ///
  ///
  /// **What the difference between this method and [`SkipMap::mmap_anon`]?**
  ///
  /// 1. This method will use an `AlignedVec` ensures we are working within Rust's memory safety guarantees.
  ///    Even if we are working with raw pointers with `Box::into_raw`,
  ///    the backend ARENA will reclaim the ownership of this memory by converting it back to a `Box`
  ///    when dropping the backend ARENA. Since `AlignedVec` uses heap memory, the data might be more cache-friendly,
  ///    especially if you're frequently accessing or modifying it.
  ///
  /// 2. Where as [`SkipMap::mmap_anon`] will use mmap anonymous to require memory from the OS.
  ///    If you require very large contiguous memory regions, `mmap` might be more suitable because
  ///    it's more direct in requesting large chunks of memory from the OS.
  ///
  /// [`SkipMap::mmap_anon`]: #method.mmap_anon
  pub fn new() -> Result<Self, Error> {
    Self::with_options(Options::new())
  }

  /// Like [`SkipMap::new`], but with [`Options`].
  #[inline]
  pub fn with_options(opts: Options) -> Result<Self, Error> {
    Self::with_options_and_comparator(opts, Ascend)
  }

  /// Create a new memory map file backed with default options.
  ///
  /// **Note:** The capacity stands for how many memory mmaped,
  /// it does not mean the skipmap can store `cap` entries.
  ///
  /// # Safety
  /// - If trying to reopens a skiplist, then the trailer type must be the same as the previous one
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub unsafe fn map_mut<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> std::io::Result<Self> {
    Self::map_mut_with_options(path, Options::new(), open_options, mmap_options)
  }

  /// Like [`SkipMap::map_mut`], but with [`Options`].
  ///
  /// # Safety
  /// - If trying to reopens a skiplist, then the trailer type must be the same as the previous one
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub unsafe fn map_mut_with_options<P: AsRef<std::path::Path>>(
    path: P,
    opts: Options,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> std::io::Result<Self> {
    Self::map_mut_with_options_and_comparator(path, opts, open_options, mmap_options, Ascend)
  }

  /// Open an exist file and mmap it to create skipmap.
  ///
  /// # Safety
  /// - If trying to reopens a skiplist, then the trailer type must be the same as the previous one
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub unsafe fn map<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    magic_version: u16,
  ) -> std::io::Result<Self> {
    Self::map_with_comparator(path, open_options, mmap_options, Ascend, magic_version)
  }

  /// Create a new memory map backed skipmap with default options.
  ///
  /// **What the difference between this method and [`SkipMap::new`]?**
  ///
  /// 1. This method will use mmap anonymous to require memory from the OS directly.
  ///    If you require very large contiguous memory regions, this method might be more suitable because
  ///    it's more direct in requesting large chunks of memory from the OS.
  ///
  /// 2. Where as [`SkipMap::new`] will use an `AlignedVec` ensures we are working within Rust's memory safety guarantees.
  ///    Even if we are working with raw pointers with `Box::into_raw`,
  ///    the backend ARENA will reclaim the ownership of this memory by converting it back to a `Box`
  ///    when dropping the backend ARENA. Since `AlignedVec` uses heap memory, the data might be more cache-friendly,
  ///    especially if you're frequently accessing or modifying it.
  ///
  /// [`SkipMap::new`]: #method.new
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn map_anon(mmap_options: MmapOptions) -> std::io::Result<Self> {
    Self::map_anon_with_options_and_comparator(Options::new(), mmap_options, Ascend)
  }

  /// Like [`SkipMap::map_anon`], but with [`Options`].
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn map_anon_with_options(opts: Options, mmap_options: MmapOptions) -> std::io::Result<Self> {
    Self::map_anon_with_options_and_comparator(opts, mmap_options, Ascend)
  }
}

impl<C> SkipMap<C> {
  /// Returns the underlying ARENA allocator used by the skipmap.
  ///
  /// This is a low level API, you should not use this method unless you know what you are doing.
  ///
  /// By default, `skl` does not do any forward and backward compatibility checks when using file backed memory map,
  /// so this will allow the users to access the ARENA allocator directly, and allocate some bytes or structures
  /// to help them implement forward and backward compatibility checks.
  ///
  /// # Example
  ///
  /// ```ignore
  /// use skl::{unsync::map::SkipMap, OpenOptions, MmapOptinos};
  ///
  /// const MAGIC_TEXT: u32 = u32::from_le_bytes(*b"al8n");
  ///
  /// struct Meta {
  ///   magic: u32,
  ///   version: u32,
  /// }
  ///
  /// let map = SkipMap::map_mut(
  ///   "/path/to/file",
  ///   OpenOptions::create_new(Some(1000)).read(true).write(true),
  ///   MmapOptions::default(),
  /// ).unwrap();
  /// let arena = map.allocater();
  /// let mut meta = arena.alloc::<Meta>();
  ///
  /// // Safety: Meta does not require any drop, so it is safe to detach it from the ARENA.
  /// unsafe { meta.detach(); }
  /// meta.write(Meta { magic: MAGIC_TEXT, version: 1 }); // now the meta info is persisted to the file.
  /// ```
  #[inline]
  pub fn allocator(&self) -> &Arena {
    self.0.allocator()
  }

  /// Returns the offset of the data section in the `SkipMap`.
  ///
  /// By default, `SkipMap` will allocate meta, head node, and tail node in the ARENA,
  /// and the data section will be allocated after the tail node.
  ///
  /// This method will return the offset of the data section in the ARENA.
  #[inline]
  pub const fn data_offset(&self) -> usize {
    self.0.data_offset()
  }

  /// Returns the magic version number of the [`SkipMap`].
  ///
  /// This value can be used to check the compatibility for application using [`SkipMap`].
  #[inline]
  pub fn magic_version(&self) -> u16 {
    self.0.magic_version()
  }

  /// Returns the height of the highest tower within any of the nodes that
  /// have ever been allocated as part of this skiplist.
  #[inline]
  pub fn height(&self) -> u8 {
    self.0.height()
  }

  /// Returns the number of remaining bytes can be allocated by the arena.
  #[inline]
  pub fn remaining(&self) -> usize {
    self.0.remaining()
  }

  /// Returns the number of bytes that have allocated from the arena.
  #[inline]
  pub fn allocated(&self) -> usize {
    self.0.allocated()
  }

  /// Returns the capacity of the arena.
  #[inline]
  pub fn capacity(&self) -> usize {
    self.0.capacity()
  }

  /// Returns the number of entries in the skipmap.
  #[inline]
  pub fn len(&self) -> usize {
    self.0.len()
  }

  /// Returns true if the skipmap is empty.
  #[inline]
  pub fn is_empty(&self) -> bool {
    self.0.is_empty()
  }

  /// Gets the number of pointers to this `SkipMap` similar to [`Arc::strong_count`](std::sync::Arc::strong_count).
  #[inline]
  pub fn refs(&self) -> usize {
    self.0.refs()
  }

  /// Returns how many bytes are discarded by the ARENA.
  #[inline]
  pub fn discarded(&self) -> u32 {
    self.0.discarded()
  }

  /// Returns the comparator used to compare keys.
  #[inline]
  pub const fn comparator(&self) -> &C {
    self.0.comparator()
  }

  /// Returns a random generated height.
  ///
  /// This method is useful when you want to check if the underlying allocator can allocate a node.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::unsync::map::SkipMap;
  ///
  /// let map = SkipMap::new().unwrap();
  /// let height = map.random_height();
  ///
  /// let needed = SkipMap::estimated_node_size(height, b"k1".len() as u32, b"k2".len() as u32);
  /// ```
  #[inline]
  pub fn random_height(&self) -> Height {
    self.0.random_height()
  }

  /// Returns the estimated size of a node with the given height and key/value sizes.
  ///
  /// **Note**: The returned size is only an estimate and may not be accurate, which means that the actual size is less than or equal to the returned size.
  #[inline]
  pub fn estimated_node_size(height: Height, key_size: impl Into<usize>, value_size: u32) -> usize {
    SkipList::<C>::estimated_node_size(height, key_size, value_size)
  }

  /// Like [`SkipMap::new`], but with a custom [`Comparator`].
  #[inline]
  pub fn with_comparator(cmp: C) -> Result<Self, Error> {
    Self::with_options_and_comparator(Options::new(), cmp)
  }

  /// Like [`SkipMap::new`], but with [`Options`] and a custom [`Comparator`].
  #[inline]
  pub fn with_options_and_comparator(opts: Options, cmp: C) -> Result<Self, Error> {
    SkipList::with_options_and_comparator(opts, cmp).map(Self)
  }

  /// Like [`SkipMap::map_mut`], but with a custom [`Comparator`].
  ///
  /// # Safety
  /// - If trying to reopens a skiplist, then the trailer type must be the same as the previous one
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub unsafe fn map_mut_with_comparator<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    cmp: C,
  ) -> std::io::Result<Self> {
    Self::map_mut_with_options_and_comparator(path, Options::new(), open_options, mmap_options, cmp)
  }

  /// Like [`SkipMap::map_mut`], but with [`Options`] and a custom [`Comparator`].
  ///
  /// # Safety
  /// - If trying to reopens a skiplist, then the trailer type must be the same as the previous one
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub unsafe fn map_mut_with_options_and_comparator<P: AsRef<std::path::Path>>(
    path: P,
    opts: Options,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    cmp: C,
  ) -> std::io::Result<Self> {
    SkipList::map_mut_with_options_and_comparator(path, opts, open_options, mmap_options, cmp)
      .map(Self)
  }

  /// Like [`SkipMap::map_mut`], but with [`Options`], a custom [`Comparator`] and a [`PathBuf`](std::path::PathBuf) builder.
  ///
  /// # Safety
  /// - If trying to reopens a skiplist, then the trailer type must be the same as the previous one
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub unsafe fn map_mut_with_options_and_comparator_and_path_builder<PB, E>(
    path_builder: PB,
    opts: Options,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    cmp: C,
  ) -> Result<Self, either::Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    SkipList::map_mut_with_options_and_comparator_and_path_builder(
      path_builder,
      opts,
      open_options,
      mmap_options,
      cmp,
    )
    .map(Self)
  }

  /// Like [`SkipMap::map`], but with a custom [`Comparator`].
  ///
  /// # Safety
  /// - If trying to reopens a skiplist, then the trailer type must be the same as the previous one
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub unsafe fn map_with_comparator<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    cmp: C,
    magic_version: u16,
  ) -> std::io::Result<Self> {
    SkipList::map_with_comparator(path, open_options, mmap_options, cmp, magic_version).map(Self)
  }

  /// Like [`SkipMap::map`], but with a custom [`Comparator`] and a [`PathBuf`](std::path::PathBuf) builder.
  ///
  /// # Safety
  /// - If trying to reopens a skiplist, then the trailer type must be the same as the previous one
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub unsafe fn map_with_comparator_and_path_builder<PB, E>(
    path_builder: PB,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    cmp: C,
    magic_version: u16,
  ) -> Result<Self, either::Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    SkipList::map_with_comparator_and_path_builder(
      path_builder,
      open_options,
      mmap_options,
      cmp,
      magic_version,
    )
    .map(Self)
  }

  /// Like [`SkipMap::map_anon`], but with a custom [`Comparator`].
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub fn map_anon_with_comparator(mmap_options: MmapOptions, cmp: C) -> std::io::Result<Self> {
    Self::map_anon_with_options_and_comparator(Options::new(), mmap_options, cmp)
  }

  /// Like [`SkipMap::map_anon`], but with [`Options`] and a custom [`Comparator`].
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub fn map_anon_with_options_and_comparator(
    opts: Options,
    mmap_options: MmapOptions,
    cmp: C,
  ) -> std::io::Result<Self> {
    SkipList::map_anon_with_options_and_comparator(opts, mmap_options, cmp).map(Self)
  }

  /// Clear the skiplist to empty and re-initialize.
  ///
  /// # Safety
  /// - The current pointers get from the ARENA cannot be used anymore after calling this method.
  /// - This method is not thread-safe.
  ///
  /// # Example
  ///
  /// Undefine behavior:
  ///
  /// ```ignore
  /// let map = SkipMap::new().unwrap();
  ///
  /// map.insert(1u8, b"hello", b"world").unwrap();
  ///
  /// let data = map.get(b"hello").unwrap();
  ///
  /// map.clear().unwrap();
  ///
  /// let w = data[0]; // undefined behavior
  /// ```
  pub unsafe fn clear(&mut self) -> Result<(), Error> {
    self.0.clear()
  }

  /// Rewind the underlying [`Arena`] to the given position.
  ///
  /// It is common to use this method to rewind the ARENA to a previous state after a failed operation.
  ///
  /// # Safety
  /// - If the current position is larger than the given position,
  ///   then the memory between the current position and the given position will be reclaimed,
  ///   so must ensure the memory chunk between the current position and the given position will not
  ///   be accessed anymore.
  /// - This method is not thread safe.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{unsync::map::SkipMap, ArenaPosition};
  ///
  /// let map = SkipMap::new().unwrap();
  ///
  /// let allocated = map.allocated();
  ///
  /// {
  ///   let n1 = map.allocate(0u8, b"hello", b"world").unwrap();
  ///   let n2 = map.allocate(0u8, b"foo", b"bar").unwrap();
  /// }
  ///
  /// let intermediate = map.allocated();
  /// assert!(intermediate > allocated);
  ///
  /// // some conditions are failed
  /// // rewind the ARENA to the position before the failed operation
  /// unsafe { map.rewind(ArenaPosition::Start(allocated as u32)); }
  ///
  /// assert_eq!(map.allocated(), allocated);
  /// ```
  pub unsafe fn rewind(&self, pos: ArenaPosition) {
    self.0.rewind(pos)
  }

  /// Flushes outstanding memory map modifications to disk.
  ///
  /// When this method returns with a non-error result,
  /// all outstanding changes to a file-backed memory map are guaranteed to be durably stored.
  /// The file's metadata (including last modification timestamp) may not be updated.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn flush(&self) -> std::io::Result<()> {
    self.0.flush()
  }

  /// Asynchronously flushes outstanding memory map modifications to disk.
  ///
  /// This method initiates flushing modified pages to durable storage, but it will not wait for
  /// the operation to complete before returning. The file's metadata (including last
  /// modification timestamp) may not be updated.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn flush_async(&self) -> std::io::Result<()> {
    self.0.flush_async()
  }
}

impl<C: Comparator> SkipMap<C> {
  /// Returns `true` if the key exists in the map. 
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::unsync::map::SkipMap;
  ///
  /// let map = SkipMap::new().unwrap();
  ///
  /// map.insert(0u8, b"hello", b"world").unwrap();
  ///
  /// map.get_or_remove(1u8, b"hello").unwrap();
  ///
  /// assert!(!map.contains_key(1u8, b"hello"));
  /// ```
  #[inline]
  pub fn contains_key<'a, 'b: 'a>(&'a self, key: &'b [u8]) -> bool {
    self.0.contains_key(MIN_VERSION, key)
  }

  /// Returns the first entry in the map.
  pub fn first(&self) -> Option<EntryRef<'_, Allocator>> {
    self.0.first(MIN_VERSION)
  }

  /// Returns the last entry in the map.
  pub fn last(&self) -> Option<EntryRef<'_, Allocator>> {
    self.0.last(MIN_VERSION)
  }

  /// Returns the value associated with the given key, if it exists.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::unsync::map::SkipMap;
  ///
  /// let map = SkipMap::new().unwrap();
  ///
  /// map.insert(0u8, b"hello", b"world").unwrap();
  ///
  /// let ent = map.get(0u8, b"hello").unwrap();
  /// assert_eq!(ent.value(), b"world");
  ///
  /// map.get_or_remove(1u8, b"hello").unwrap();
  ///
  /// assert!(map.get(1u8, b"hello").is_none());
  /// ```
  pub fn get<'a, 'b: 'a>(&'a self, key: &'b [u8]) -> Option<EntryRef<'a, Allocator>> {
    self.0.get(MIN_VERSION, key)
  }

  /// Returns an `EntryRef` pointing to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  pub fn upper_bound<'a, 'b: 'a>(
    &'a self,
    upper: Bound<&'b [u8]>,
  ) -> Option<EntryRef<'a, Allocator>> {
    self.0.upper_bound(MIN_VERSION, upper)
  }

  /// Returns an `EntryRef` pointing to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  pub fn lower_bound<'a, 'b: 'a>(
    &'a self,
    lower: Bound<&'b [u8]>,
  ) -> Option<EntryRef<'a, Allocator>> {
    self.0.lower_bound(MIN_VERSION, lower)
  }

  /// Returns a new iterator, this iterator will yield the latest version of all entries in the map less or equal to the given version.
  #[inline]
  pub fn iter(&self) -> Iter<Allocator, C> {
    self.0.iter(MIN_VERSION)
  }

  /// Returns a new iterator, this iterator will yield all versions for all entries in the map less or equal to the given version.
  #[inline]
  pub fn iter_all_versions(&self) -> AllVersionsIter<Allocator, C> {
    self.0.iter_all_versions(MIN_VERSION)
  }

  /// Returns a iterator that within the range, this iterator will yield the latest version of all entries in the range less or equal to the given version.
  #[inline]
  pub fn range<'a, Q, R>(&'a self, range: R) -> Iter<'a, Allocator, C, Q, R>
  where
    Q: ?Sized + Borrow<[u8]>,
    R: RangeBounds<Q> + 'a,
  {
    self.0.range(MIN_VERSION, range)
  }

  /// Returns a iterator that within the range, this iterator will yield all versions for all entries in the range less or equal to the given version.
  #[inline]
  pub fn range_all_versions<'a, Q, R>(&'a self, range: R) -> AllVersionsIter<'a, Allocator, C, Q, R>
  where
    Q: ?Sized + Borrow<[u8]>,
    R: RangeBounds<Q> + 'a,
  {
    self.0.range_all_versions(MIN_VERSION, range)
  }
}

impl<C: Comparator> SkipMap<C> {
  /// Upserts a new key-value pair if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert`](SkipMap::get_or_insert), this method will update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  #[inline]
  pub fn insert<'a, 'b: 'a>(
    &'a self,
    key: &'b [u8],
    value: &'b [u8],
  ) -> Result<Option<EntryRef<'a, Allocator>>, Error> {
    self.0.insert(MIN_VERSION, key, value, ())
  }

  /// Upserts a new key-value pair at the given height if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert_at_height`](SkipMap::get_or_insert_at_height), this method will update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::unsync::map::SkipMap;
  ///
  /// let map = SkipMap::new().unwrap();
  ///
  /// let height = map.random_height();
  /// map.insert_at_height(Version::new(), height, b"hello", b"world").unwrap();
  /// ```
  #[inline]
  pub fn insert_at_height<'a, 'b: 'a>(
    &'a self,
    height: Height,
    key: &'b [u8],
    value: &'b [u8],
  ) -> Result<Option<EntryRef<'a, Allocator>>, Error> {
    self.0.insert_at_height(MIN_VERSION, height, key, value, ())
  }

  /// Upserts a new key if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert_with_value_builder`](SkipMap::get_or_insert_with_value_builder), this method will update the value if the key with the given version already exists.
  ///
  /// This method is useful when you want to insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// A placeholder will be inserted first, then you will get an [`VacantBuffer`],
  /// and you must fill the buffer with bytes later in the closure.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{unsync::map::SkipMap, ValueBuilder};
  ///
  /// struct Person {
  ///   id: u32,
  ///   name: String,
  /// }
  ///
  /// impl Person {
  ///   fn encoded_size(&self) -> usize {
  ///     4 + self.name.len()
  ///   }
  /// }
  ///
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = SkipMap::new().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// l.insert_with_value_builder::<core::convert::Infallible>(1.into(), b"alice", vb)
  /// .unwrap();
  /// ```
  #[inline]
  pub fn insert_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, Allocator>>, Either<E, Error>> {
    self.0.insert_at_height_with_value_builder(
      MIN_VERSION,
      self.random_height(),
      key,
      value_builder,
      (),
    )
  }

  /// Upserts a new key if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert_with_value_builder`](SkipMap::get_or_insert_with_value_builder), this method will update the value if the key with the given version already exists.
  ///
  /// This method is useful when you want to insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// A placeholder will be inserted first, then you will get an [`VacantBuffer`],
  /// and you must fill the buffer with bytes later in the closure.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{unsync::map::SkipMap, ValueBuilder};
  ///
  /// struct Person {
  ///   id: u32,
  ///   name: String,
  /// }
  ///
  /// impl Person {
  ///   fn encoded_size(&self) -> usize {
  ///     4 + self.name.len()
  ///   }
  /// }
  ///
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = SkipMap::new().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.insert_at_height_with_value_builder::<core::convert::Infallible>(1.into(), height, b"alice", vb)
  /// .unwrap();
  /// ```
  pub fn insert_at_height_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    height: Height,
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, Allocator>>, Either<E, Error>> {
    self
      .0
      .insert_at_height_with_value_builder(MIN_VERSION, height, key, value_builder, ())
  }

  /// Inserts a new key-value pair if it does not yet exist.
  ///
  /// Unlike [`insert`](SkipMap::insert), this method will not update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully get_or_inserted.
  /// - Returns `Ok(Some(_))` if the key with the given version already exists.
  #[inline]
  pub fn get_or_insert<'a, 'b: 'a>(
    &'a self,
    key: &'b [u8],
    value: &'b [u8],
  ) -> Result<Option<EntryRef<'a, Allocator>>, Error> {
    self
      .0
      .get_or_insert_at_height(MIN_VERSION, self.random_height(), key, value, ())
  }

  /// Inserts a new key-value pair at height if it does not yet exist.
  ///
  /// Unlike [`insert_at_height`](SkipMap::insert_at_height), this method will not update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully get_or_inserted.
  /// - Returns `Ok(Some(_))` if the key with the given version already exists.
  pub fn get_or_insert_at_height<'a, 'b: 'a>(
    &'a self,
    height: Height,
    key: &'b [u8],
    value: &'b [u8],
  ) -> Result<Option<EntryRef<'a, Allocator>>, Error> {
    self
      .0
      .get_or_insert_at_height(MIN_VERSION, height, key, value, ())
  }

  /// Inserts a new key if it does not yet exist.
  ///
  /// Unlike [`insert_with_value_builder`](SkipMap::insert_with_value_builder), this method will not update the value if the key with the given version already exists.
  ///
  /// This method is useful when you want to get_or_insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// A placeholder will be inserted first, then you will get an [`VacantBuffer`],
  /// and you must fill the buffer with bytes later in the closure.
  ///
  /// - Returns `Ok(None)` if the key was successfully get_or_inserted.
  /// - Returns `Ok(Some(_))` if the key with the given version already exists.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{unsync::map::SkipMap, ValueBuilder};
  ///
  /// struct Person {
  ///   id: u32,
  ///   name: String,
  /// }
  ///
  /// impl Person {
  ///   fn encoded_size(&self) -> usize {
  ///     4 + self.name.len()
  ///   }
  /// }
  ///
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = SkipMap::new().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  /// l.get_or_insert_with_value_builder::<core::convert::Infallible>(1.into(), b"alice", vb)
  /// .unwrap();
  /// ```
  #[inline]
  pub fn get_or_insert_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, Allocator>>, Either<E, Error>> {
    self.get_or_insert_at_height_with_value_builder(self.random_height(), key, value_builder)
  }

  /// Inserts a new key if it does not yet exist.
  ///
  /// Unlike [`insert_at_height_with_value_builder`](SkipMap::insert_at_height_with_value_builder), this method will not update the value if the key with the given version already exists.
  ///
  /// This method is useful when you want to get_or_insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// A placeholder will be inserted first, then you will get an [`VacantBuffer`],
  /// and you must fill the buffer with bytes later in the closure.
  ///
  /// - Returns `Ok(None)` if the key was successfully get_or_inserted.
  /// - Returns `Ok(Some(_))` if the key with the given version already exists.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{unsync::map::SkipMap, ValueBuilder};
  ///
  /// struct Person {
  ///   id: u32,
  ///   name: String,
  /// }
  ///
  /// impl Person {
  ///   fn encoded_size(&self) -> usize {
  ///     4 + self.name.len()
  ///   }
  /// }
  ///
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = SkipMap::new().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.get_or_insert_at_height_with_value_builder::<core::convert::Infallible>(1.into(), height, b"alice", vb)
  /// .unwrap();
  /// ```
  #[inline]
  pub fn get_or_insert_at_height_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    height: Height,
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, Allocator>>, Either<E, Error>> {
    self
      .0
      .get_or_insert_at_height_with_value_builder(MIN_VERSION, height, key, value_builder, ())
  }

  /// Upserts a new key if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert_with_builders`](SkipMap::get_or_insert_with_builders), this method will update the value if the key with the given version already exists.
  ///
  /// This method is useful when you want to insert a key and you know the key size and value size but you do not have the key and value
  /// at this moment.
  ///
  /// A placeholder will be inserted first, then you will get an [`VacantBuffer`],
  /// and you must fill the buffer with bytes later in the closure.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{unsync::map::SkipMap, KeyBuilder, ValueBuilder};
  ///
  /// struct Person {
  ///   id: u32,
  ///   name: String,
  /// }
  ///
  /// impl Person {
  ///   fn encoded_size(&self) -> usize {
  ///     4 + self.name.len()
  ///   }
  /// }
  ///
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = SkipMap::new().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |mut key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// l.insert_with_builders::<core::convert::Infallible>(1.into(), kb, vb)
  /// .unwrap();
  /// ```
  #[inline]
  pub fn insert_with_builders<'a, E>(
    &'a self,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, Allocator>>, Either<E, Error>> {
    self.0.insert_at_height_with_builders(
      MIN_VERSION,
      self.random_height(),
      key_builder,
      value_builder,
      (),
    )
  }

  /// Upserts a new key if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert_with_builders_and_trailer`](SkipMap::get_or_insert_with_builders_and_trailer), this method will update the value if the key with the given version already exists.
  ///
  /// This method is useful when you want to insert a key and you know the key size and value size but you do not have the key and value
  /// at this moment.
  ///
  /// A placeholder will be inserted first, then you will get an [`VacantBuffer`],
  /// and you must fill the buffer with bytes later in the closure.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{unsync::map::SkipMap, KeyBuilder, ValueBuilder};
  ///
  /// struct Person {
  ///   id: u32,
  ///   name: String,
  /// }
  ///
  /// impl Person {
  ///   fn encoded_size(&self) -> usize {
  ///     4 + self.name.len()
  ///   }
  /// }
  ///
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = SkipMap::new().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |mut key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.insert_at_height_with_builders::<core::convert::Infallible>(1.into(), height, kb, vb)
  /// .unwrap();
  /// ```
  #[inline]
  pub fn insert_at_height_with_builders<'a, E>(
    &'a self,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, Allocator>>, Either<E, Error>> {
    self
      .0
      .insert_at_height_with_builders(MIN_VERSION, height, key_builder, value_builder, ())
  }

  /// Inserts a new key if it does not yet exist.
  ///
  /// Unlike [`insert_with_builders`](SkipMap::insert_with_builders), this method will not update the value if the key with the given version already exists.
  ///
  /// This method is useful when you want to get_or_insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// A placeholder will be inserted first, then you will get an [`VacantBuffer`],
  /// and you must fill the buffer with bytes later in the closure.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{unsync::map::SkipMap, KeyBuilder, ValueBuilder};
  ///
  /// struct Person {
  ///   id: u32,
  ///   name: String,
  /// }
  ///
  /// impl Person {
  ///   fn encoded_size(&self) -> usize {
  ///     4 + self.name.len()
  ///   }
  /// }
  ///
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = SkipMap::new().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |mut key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// l.get_or_insert_with_builders::<core::convert::Infallible>(1.into(), kb, vb)
  /// .unwrap();
  /// ```
  #[inline]
  pub fn get_or_insert_with_builders<'a, E>(
    &'a self,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, Allocator>>, Either<E, Error>> {
    self.0.get_or_insert_at_height_with_builders(
      MIN_VERSION,
      self.random_height(),
      key_builder,
      value_builder,
      (),
    )
  }

  /// Inserts a new key if it does not yet exist.
  ///
  /// Unlike [`insert_at_height_with_builders`](SkipMap::insert_at_height_with_builders), this method will not update the value if the key with the given version already exists.
  ///
  /// This method is useful when you want to get_or_insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// A placeholder will be inserted first, then you will get an [`VacantBuffer`],
  /// and you must fill the buffer with bytes later in the closure.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{unsync::map::SkipMap, KeyBuilder, ValueBuilder};
  ///
  /// struct Person {
  ///   id: u32,
  ///   name: String,
  /// }
  ///
  /// impl Person {
  ///   fn encoded_size(&self) -> usize {
  ///     4 + self.name.len()
  ///   }
  /// }
  ///
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = SkipMap::new().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |mut key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.get_or_insert_at_height_with_builders::<core::convert::Infallible>(1.into(), height, kb, vb)
  /// .unwrap();
  /// ```
  pub fn get_or_insert_at_height_with_builders<'a, E>(
    &'a self,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, Allocator>>, Either<E, Error>> {
    self.0.get_or_insert_at_height_with_builders(
      MIN_VERSION,
      height,
      key_builder,
      value_builder,
      (),
    )
  }

  /// Removes the key-value pair if it exists. A CAS operation will be used to ensure the operation is atomic.
  ///
  /// Unlike [`get_or_remove`](SkipMap::get_or_remove), this method will remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)`:
  ///   - if the remove operation is successful or the key is marked in remove status by other threads.
  /// - Returns `Ok(Either::Right(current))` if the key with the given version already exists
  ///   and the entry is not successfully removed because of an update on this entry happens in another thread.
  #[inline]
  pub fn compare_remove<'a, 'b: 'a>(
    &'a self,
    key: &'b [u8],
    success: Ordering,
    failure: Ordering,
  ) -> Result<Option<EntryRef<'a, Allocator>>, Error> {
    self.compare_remove_at_height(self.random_height(), key, success, failure)
  }

  /// Removes the key-value pair if it exists. A CAS operation will be used to ensure the operation is atomic.
  ///
  /// Unlike [`get_or_remove_at_height`](SkipMap::get_or_remove_at_height), this method will remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)`:
  ///   - if the remove operation is successful or the key is marked in remove status by other threads.
  /// - Returns `Ok(Either::Right(current))` if the key with the given version already exists
  ///   and the entry is not successfully removed because of an update on this entry happens in another thread.
  pub fn compare_remove_at_height<'a, 'b: 'a>(
    &'a self,
    height: Height,
    key: &'b [u8],
    success: Ordering,
    failure: Ordering,
  ) -> Result<Option<EntryRef<'a, Allocator>>, Error> {
    self
      .0
      .compare_remove_at_height(MIN_VERSION, height, key, (), success, failure)
  }

  /// Gets or removes the key-value pair if it exists.
  /// Unlike [`compare_remove`](SkipMap::compare_remove), this method will not remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key does not exist.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists.
  #[inline]
  pub fn get_or_remove<'a, 'b: 'a>(
    &'a self,
    key: &'b [u8],
  ) -> Result<Option<EntryRef<'a, Allocator>>, Error> {
    self.get_or_remove_at_height(self.random_height(), key)
  }

  /// Gets or removes the key-value pair if it exists.
  /// Unlike [`compare_remove_at_height`](SkipMap::compare_remove_at_height), this method will not remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key does not exist.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::unsync::map::SkipMap;
  ///
  /// let map = SkipMap::new().unwrap();
  ///
  /// map.insert(0u8, b"hello", b"world").unwrap();
  ///
  /// let height = map.random_height();
  /// map.get_or_remove_at_height(0u8, height, b"hello").unwrap();
  /// ```
  #[inline]
  pub fn get_or_remove_at_height<'a, 'b: 'a>(
    &'a self,
    height: Height,
    key: &'b [u8],
  ) -> Result<Option<EntryRef<'a, Allocator>>, Error> {
    self.0.get_or_remove_at_height(MIN_VERSION, height, key, ())
  }

  /// Gets or removes the key-value pair if it exists.
  /// Unlike [`compare_remove_with_builder_and_trailer`](SkipMap::compare_remove_with_builder_and_trailer), this method will not remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key does not exist.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists.
  ///
  /// This method is useful when you want to get_or_remove a key and you know the key size but you do not have the key
  /// at this moment.
  ///
  /// A placeholder will be inserted first, then you will get an [`VacantBuffer`],
  /// and you must fill the buffer with bytes later in the closure.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{unsync::map::SkipMap, KeyBuilder};
  ///
  /// struct Person {
  ///   id: u32,
  ///   name: String,
  /// }
  ///
  /// impl Person {
  ///   fn encoded_size(&self) -> usize {
  ///     4 + self.name.len()
  ///   }
  /// }
  ///
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = SkipMap::new().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |mut key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// });
  /// l.get_or_remove_with_builder::<core::convert::Infallible>(1.into(), kb, Ttl::new(std::time::Duration::from_seconds(60)))
  /// .unwrap();
  /// ```
  pub fn get_or_remove_with_builder<'a, 'b: 'a, E>(
    &'a self,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, Allocator>>, Either<E, Error>> {
    self
      .0
      .get_or_remove_at_height_with_builder(MIN_VERSION, self.random_height(), key_builder, ())
  }

  /// Gets or removes the key-value pair if it exists.
  /// Unlike [`compare_remove_at_height_with_builder_and_trailer`](SkipMap::compare_remove_at_height_with_builder_and_trailer), this method will not remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key does not exist.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists.
  ///
  /// This method is useful when you want to get_or_remove a key and you know the key size but you do not have the key
  /// at this moment.
  ///
  /// A placeholder will be inserted first, then you will get an [`VacantBuffer`],
  /// and you must fill the buffer with bytes later in the closure.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{unsync::map::SkipMap, KeyBuilder};
  ///
  /// struct Person {
  ///   id: u32,
  ///   name: String,
  /// }
  ///
  /// impl Person {
  ///   fn encoded_size(&self) -> usize {
  ///     4 + self.name.len()
  ///   }
  /// }
  ///
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = SkipMap::new().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |mut key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// });
  /// let height = l.random_height();
  /// l.get_or_remove_at_height_with_builder::<core::convert::Infallible>(1.into(), height, kb)
  /// .unwrap();
  /// ```
  pub fn get_or_remove_at_height_with_builder<'a, 'b: 'a, E>(
    &'a self,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, Allocator>>, Either<E, Error>> {
    self
      .0
      .get_or_remove_at_height_with_builder(MIN_VERSION, height, key_builder, ())
  }
}
