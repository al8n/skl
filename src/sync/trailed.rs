use core::{borrow::Borrow, marker::PhantomData};

use super::*;

use base::{EntryRef, Iter};

type Allocator<T> = GenericAllocator<Meta, TrailedNode<T>, Arena>;
type SkipList<T, C> = base::SkipList<Allocator<T>, C>;

node_pointer!(TrailedNode<T>);

/// A node that supports trailer.
#[repr(C)]
pub struct TrailedNode<T> {
  // A byte slice is 24 bytes. We are trying to save space here.
  /// Multiple parts of the value are encoded as a single u64 so that it
  /// can be atomically loaded and stored:
  ///   value offset: u32 (bits 0-31)
  ///   value size  : u32 (bits 32-63)
  value: AtomicValuePointer,
  // Immutable. No need to lock to access key.
  key_offset: u32,
  // Immutable. No need to lock to access key.
  key_size_and_height: u32,
  trailer: PhantomData<T>,
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

impl<T> core::fmt::Debug for TrailedNode<T> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    let (key_size, height) = decode_key_size_and_height(self.key_size_and_height);
    let (value_offset, value_size) = decode_value_pointer(self.value.0.load(Ordering::Relaxed));
    f.debug_struct("Node")
      .field("value_offset", &value_offset)
      .field("value_size", &value_size)
      .field("key_offset", &self.key_offset)
      .field("key_size", &key_size)
      .field("height", &height)
      .finish()
  }
}

impl<T: Trailer> WithTrailer for TrailedNode<T> {}

impl<T: Trailer> Node for TrailedNode<T> {
  type Link = Link;

  type Trailer = T;

  type ValuePointer = AtomicValuePointer;

  type Pointer = NodePointer<Self::Trailer>;

  fn full(value_offset: u32, max_height: u8) -> Self {
    Self {
      value: AtomicValuePointer::new(value_offset, 0),
      key_offset: 0,
      key_size_and_height: encode_key_size_and_height(0, max_height),
      trailer: PhantomData,
    }
  }

  #[inline]
  fn value_pointer(&self) -> &Self::ValuePointer {
    &self.value
  }

  #[inline]
  fn set_value_pointer(&mut self, offset: u32, size: u32) {
    self.value = AtomicValuePointer::new(offset, size);
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
pub struct SkipMap<T: Trailer = (), C = Ascend>(SkipList<T, C>);

impl<T: Trailer, C: Clone> Clone for SkipMap<T, C> {
  #[inline]
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<T: Trailer> SkipMap<T> {
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
  /// # Safety
  /// - If trying to reopens a skiplist, then the trailer type must be the same as the previous one
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

  #[cfg(all(test, feature = "std"))]
  #[inline]
  pub(crate) fn with_yield_now(self) -> Self {
    Self(self.0.with_yield_now())
  }
}

impl<T: Trailer, C> SkipMap<T, C> {
  /// Returns the path of the mmap file, only returns `Some` when the ARENA is backed by a mmap file.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub fn path(&self) -> Option<&std::sync::Arc<std::path::PathBuf>> {
    self.0.arena.path()
  }

  /// Sets remove on drop, only works on mmap with a file backend.
  ///
  /// Default is `false`.
  ///
  /// > **WARNING:** Once set to `true`, the backed file will be removed when the allocator is dropped, even though the file is opened in
  /// > read-only mode.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub fn remove_on_drop(&self, val: bool) {
    self.0.remove_on_drop(val);
  }

  /// Returns the offset of the data section in the `SkipMap`.
  ///
  /// By default, `SkipMap` will allocate meta, head node, and tail node in the ARENA,
  /// and the data section will be allocated after the tail node.
  ///
  /// This method will return the offset of the data section in the ARENA.
  #[inline]
  pub fn data_offset(&self) -> usize {
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
  pub fn comparator(&self) -> &C {
    self.0.comparator()
  }

  /// Returns a random generated height.
  ///
  /// This method is useful when you want to check if the underlying allocator can allocate a node.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::sync::trailed::SkipMap;
  ///
  /// let map = SkipMap::<u64>::new().unwrap();
  /// let height = map.random_height();
  ///
  /// let needed = SkipMap::<u64>::estimated_node_size(height, b"k1".len(), b"k2".len());
  /// ```
  #[inline]
  pub fn random_height(&self) -> Height {
    self.0.random_height()
  }

  /// Returns the estimated size of a node with the given height and key/value sizes.
  ///
  /// **Note**: The returned size is only an estimate and may not be accurate, which means that the actual size is less than or equal to the returned size.
  #[inline]
  pub fn estimated_node_size(height: Height, key_size: usize, value_size: usize) -> usize {
    SkipList::<T, C>::estimated_node_size(height, key_size, value_size)
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
  /// map.insert(b"hello", b"world").unwrap();
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

impl<T: Trailer, C: Comparator> SkipMap<T, C> {
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
    trailer: T,
  ) -> Result<Option<EntryRef<'a, Allocator<T>>>, Error> {
    self
      .0
      .insert_at_height(MIN_VERSION, self.random_height(), key, value, trailer)
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
  /// use skl::{sync::trailed::SkipMap, Ascend};
  ///
  /// let map = SkipMap::<u64>::new().unwrap();
  ///
  /// let height = map.random_height();
  /// map.insert_at_height(height, b"hello", b"world", 10).unwrap();
  /// ```
  pub fn insert_at_height<'a, 'b: 'a>(
    &'a self,
    height: Height,
    key: &'b [u8],
    value: &'b [u8],
    trailer: T,
  ) -> Result<Option<EntryRef<'a, Allocator<T>>>, Error> {
    self
      .0
      .insert_at_height(MIN_VERSION, height, key, value, trailer)
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
  /// use skl::{sync::trailed::SkipMap, ValueBuilder};
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
  /// let l = SkipMap::<u64>::new().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// l.insert_with_value_builder::<core::convert::Infallible>(b"alice", vb, 10)
  /// .unwrap();
  /// ```
  #[inline]
  pub fn insert_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, Allocator<T>>>, Either<E, Error>> {
    self.0.insert_at_height_with_value_builder(
      MIN_VERSION,
      self.random_height(),
      key,
      value_builder,
      trailer,
    )
  }

  /// Upserts a new key if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert_at_height_with_value_builder`](SkipMap::get_or_insert_at_height_with_value_builder), this method will update the value if the key with the given version already exists.
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
  /// use skl::{sync::trailed::SkipMap, ValueBuilder};
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
  /// let l = SkipMap::<u64>::new().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.insert_at_height_with_value_builder::<core::convert::Infallible>(height, b"alice", vb, 10)
  /// .unwrap();
  /// ```
  pub fn insert_at_height_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    height: Height,
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, Allocator<T>>>, Either<E, Error>> {
    self
      .0
      .insert_at_height_with_value_builder(MIN_VERSION, height, key, value_builder, trailer)
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
    trailer: T,
  ) -> Result<Option<EntryRef<'a, Allocator<T>>>, Error> {
    self
      .0
      .get_or_insert_at_height(MIN_VERSION, self.random_height(), key, value, trailer)
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
    trailer: T,
  ) -> Result<Option<EntryRef<'a, Allocator<T>>>, Error> {
    self
      .0
      .get_or_insert_at_height(MIN_VERSION, height, key, value, trailer)
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
  /// use skl::{sync::trailed::SkipMap, ValueBuilder};
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
  /// let l = SkipMap::<u64>::new().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  /// l.get_or_insert_with_value_builder::<core::convert::Infallible>(b"alice", vb, 10)
  /// .unwrap();
  /// ```
  #[inline]
  pub fn get_or_insert_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, Allocator<T>>>, Either<E, Error>> {
    self.0.get_or_insert_at_height_with_value_builder(
      MIN_VERSION,
      self.random_height(),
      key,
      value_builder,
      trailer,
    )
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
  /// use skl::{sync::trailed::SkipMap, ValueBuilder};
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
  /// let l = SkipMap::<u64>::new().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.get_or_insert_at_height_with_value_builder::<core::convert::Infallible>(height, b"alice", vb, 10)
  /// .unwrap();
  /// ```
  pub fn get_or_insert_at_height_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    height: Height,
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, Allocator<T>>>, Either<E, Error>> {
    self.0.get_or_insert_at_height_with_value_builder(
      MIN_VERSION,
      height,
      key,
      value_builder,
      trailer,
    )
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
  /// use skl::{sync::trailed::SkipMap, KeyBuilder, ValueBuilder};
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
  /// let l = SkipMap::<u64>::new().unwrap();
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
  /// l.insert_with_builders::<core::convert::Infallible>(kb, vb, 10)
  /// .unwrap();
  /// ```
  #[inline]
  pub fn insert_with_builders<'a, E>(
    &'a self,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, Allocator<T>>>, Either<E, Error>> {
    self.0.insert_at_height_with_builders(
      MIN_VERSION,
      self.random_height(),
      key_builder,
      value_builder,
      trailer,
    )
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
  /// use skl::{sync::trailed::SkipMap, KeyBuilder, ValueBuilder};
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
  /// let l = SkipMap::<u64>::new().unwrap();
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
  /// l.insert_at_height_with_builders::<core::convert::Infallible>(height, kb, vb, 10)
  /// .unwrap();
  /// ```
  pub fn insert_at_height_with_builders<'a, E>(
    &'a self,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, Allocator<T>>>, Either<E, Error>> {
    self
      .0
      .insert_at_height_with_builders(MIN_VERSION, height, key_builder, value_builder, trailer)
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
  /// use skl::{sync::trailed::SkipMap, KeyBuilder, ValueBuilder};
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
  /// let l = SkipMap::<u64>::new().unwrap();
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
  /// l.get_or_insert_with_builders::<core::convert::Infallible>(kb, vb, 10)
  /// .unwrap();
  /// ```
  #[inline]
  pub fn get_or_insert_with_builders<'a, E>(
    &'a self,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, Allocator<T>>>, Either<E, Error>> {
    self.0.get_or_insert_at_height_with_builders(
      MIN_VERSION,
      self.random_height(),
      key_builder,
      value_builder,
      trailer,
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
  /// use skl::{sync::trailed::SkipMap, KeyBuilder, ValueBuilder};
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
  /// let l = SkipMap::<u64>::new().unwrap();
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
  /// l.get_or_insert_at_height_with_builders::<core::convert::Infallible>(height, kb, vb, 10)
  /// .unwrap();
  /// ```
  pub fn get_or_insert_at_height_with_builders<'a, E>(
    &'a self,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, Allocator<T>>>, Either<E, Error>> {
    self.0.get_or_insert_at_height_with_builders(
      MIN_VERSION,
      height,
      key_builder,
      value_builder,
      trailer,
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
    trailer: T,
    success: Ordering,
    failure: Ordering,
  ) -> Result<Option<EntryRef<'a, Allocator<T>>>, Error> {
    self.0.compare_remove_at_height(
      MIN_VERSION,
      self.random_height(),
      key,
      trailer,
      success,
      failure,
    )
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
    trailer: T,
    success: Ordering,
    failure: Ordering,
  ) -> Result<Option<EntryRef<'a, Allocator<T>>>, Error> {
    self
      .0
      .compare_remove_at_height(MIN_VERSION, height, key, trailer, success, failure)
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
    trailer: T,
  ) -> Result<Option<EntryRef<'a, Allocator<T>>>, Error> {
    self
      .0
      .get_or_remove_at_height(MIN_VERSION, self.random_height(), key, trailer)
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
  /// use skl::sync::trailed::SkipMap;
  ///
  /// let map = SkipMap::<u64>::new().unwrap();
  ///
  /// map.insert(b"hello", b"world", 10).unwrap();
  ///
  /// let height = map.random_height();
  /// map.get_or_remove_at_height(height, b"hello", 10).unwrap();
  /// ```
  pub fn get_or_remove_at_height<'a, 'b: 'a>(
    &'a self,
    height: Height,
    key: &'b [u8],
    trailer: T,
  ) -> Result<Option<EntryRef<'a, Allocator<T>>>, Error> {
    self
      .0
      .get_or_remove_at_height(MIN_VERSION, height, key, trailer)
  }

  /// Gets or removes the key-value pair if it exists.
  /// Unlike [`compare_remove`](SkipMap::compare_remove), this method will not remove the value if the key with the given version already exists.
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
  /// use skl::{sync::trailed::SkipMap, KeyBuilder};
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
  /// let l = SkipMap::<u64>::new().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |mut key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// });
  /// l.get_or_remove_with_builder::<core::convert::Infallible>(kb, 10)
  /// .unwrap();
  /// ```
  pub fn get_or_remove_with_builder<'a, 'b: 'a, E>(
    &'a self,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, Allocator<T>>>, Either<E, Error>> {
    self.0.get_or_remove_at_height_with_builder(
      MIN_VERSION,
      self.random_height(),
      key_builder,
      trailer,
    )
  }

  /// Gets or removes the key-value pair if it exists.
  /// Unlike [`compare_remove_at_height`](SkipMap::compare_remove_at_height), this method will not remove the value if the key with the given version already exists.
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
  /// use skl::{sync::trailed::SkipMap, KeyBuilder};
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
  /// let l = SkipMap::<u64>::new().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |mut key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// });
  /// let height = l.random_height();
  /// l.get_or_remove_at_height_with_builder::<core::convert::Infallible>(height, kb, 10)
  /// .unwrap();
  /// ```
  pub fn get_or_remove_at_height_with_builder<'a, 'b: 'a, E>(
    &'a self,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, Allocator<T>>>, Either<E, Error>> {
    self
      .0
      .get_or_remove_at_height_with_builder(MIN_VERSION, height, key_builder, trailer)
  }
}

impl<T: Trailer, C: Comparator> SkipMap<T, C> {
  /// Returns `true` if the key exists in the map.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::sync::trailed::SkipMap;
  /// use core::sync::atomic::Ordering;
  ///
  /// let map = SkipMap::<u64>::new().unwrap();
  ///
  /// map.insert(b"hello", b"world", 10).unwrap();
  ///
  /// map.compare_remove(b"hello", 10, Ordering::Relaxed, Ordering::Relaxed).unwrap();
  ///
  /// assert!(!map.contains_key(b"hello"));
  /// ```
  #[inline]
  pub fn contains_key<'a, 'b: 'a>(&'a self, key: &'b [u8]) -> bool {
    self.0.contains_key(MIN_VERSION, key)
  }

  /// Returns the first entry in the map.
  pub fn first(&self) -> Option<EntryRef<'_, Allocator<T>>> {
    self.0.first(MIN_VERSION)
  }

  /// Returns the last entry in the map.
  pub fn last(&self) -> Option<EntryRef<'_, Allocator<T>>> {
    self.0.last(MIN_VERSION)
  }

  /// Returns the value associated with the given key, if it exists.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::sync::trailed::SkipMap;
  /// use core::sync::atomic::Ordering;
  ///
  /// let map = SkipMap::<u64>::new().unwrap();
  ///
  /// map.insert(b"hello", b"world", 10).unwrap();
  ///
  /// let ent = map.get(b"hello").unwrap();
  /// assert_eq!(ent.value(), b"world");
  ///
  /// map.compare_remove(b"hello", 10, Ordering::Relaxed, Ordering::Relaxed).unwrap();
  ///
  /// assert!(map.get(b"hello").is_none());
  /// ```
  pub fn get<'a, 'b: 'a>(&'a self, key: &'b [u8]) -> Option<EntryRef<'a, Allocator<T>>> {
    self.0.get(MIN_VERSION, key)
  }

  /// Returns an `EntryRef` pointing to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  pub fn upper_bound<'a, 'b: 'a>(
    &'a self,
    upper: Bound<&'b [u8]>,
  ) -> Option<EntryRef<'a, Allocator<T>>> {
    self.0.upper_bound(MIN_VERSION, upper)
  }

  /// Returns an `EntryRef` pointing to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  pub fn lower_bound<'a, 'b: 'a>(
    &'a self,
    lower: Bound<&'b [u8]>,
  ) -> Option<EntryRef<'a, Allocator<T>>> {
    self.0.lower_bound(MIN_VERSION, lower)
  }

  /// Returns a new iterator, this iterator will yield the latest version of all entries in the map less or equal to the given version.
  #[inline]
  pub fn iter(&self) -> Iter<Allocator<T>, C> {
    self.0.iter(MIN_VERSION)
  }

  /// Returns a iterator that within the range, this iterator will yield the latest version of all entries in the range less or equal to the given version.
  #[inline]
  pub fn range<'a, Q, R>(&'a self, range: R) -> Iter<'a, Allocator<T>, C, Q, R>
  where
    Q: ?Sized + Borrow<[u8]>,
    R: RangeBounds<Q> + 'a,
  {
    self.0.range(MIN_VERSION, range)
  }
}
