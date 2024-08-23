use core::{borrow::Borrow, sync::atomic::Ordering};

use rarena_allocator::{sync::Arena, ArenaPosition};

use super::{
  base::{EntryRef, Error, Iter, SkipList},
  *,
};

use either::Either;

/// A fast, cocnurrent map implementation based on skiplist that supports forward
/// and backward iteration.
#[repr(transparent)]
pub struct SkipMap<T, C = Ascend>(SkipList<C, T>);

impl<T, C: Clone> Clone for SkipMap<T, C> {
  #[inline]
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<T> SkipMap<T> {
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
  pub unsafe fn map_anon(mmap_options: MmapOptions) -> std::io::Result<Self> {
    Self::map_anon_with_options_and_comparator(Options::new(), mmap_options, Ascend)
  }

  /// Like [`SkipMap::map_anon`], but with [`Options`].
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn map_anon_with_options(opts: Options, mmap_options: MmapOptions) -> std::io::Result<Self> {
    Self::map_anon_with_options_and_comparator(opts, mmap_options, Ascend)
  }
}

impl<T, C> SkipMap<T, C> {
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
  /// use skl::{trailed::SkipMap, OpenOptions, MmapOptinos};
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
  pub const fn allocator(&self) -> &Arena {
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

  /// Returns the version number of the [`SkipMap`].
  #[inline]
  pub const fn version(&self) -> u16 {
    self.0.magic_version()
  }

  /// Returns the magic version number of the [`SkipMap`].
  ///
  /// This value can be used to check the compatibility for application using [`SkipMap`].
  #[inline]
  pub const fn magic_version(&self) -> u16 {
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
  pub const fn capacity(&self) -> usize {
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

  /// Returns the maximum version of all entries in the map.
  #[inline]
  pub fn max_version(&self) -> u64 {
    self.0.max_version()
  }

  /// Returns the minimum version of all entries in the map.
  #[inline]
  pub fn min_version(&self) -> u64 {
    self.0.min_version()
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
  /// use skl::trailed::SkipMap;
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
    SkipList::<C, ()>::estimated_node_size(height, key_size, value_size)
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
  /// use skl::{trailed::SkipMap, ArenaPosition};
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

impl<T: Trailer, C: Comparator> SkipMap<T, C> {
  /// Allocates a new node in the [`SkipMap`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipMap::link`] or [`SkipMap::get_or_link`].
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::*;
  ///
  /// let map = SkipMap::new().unwrap();
  ///
  /// let unlinked_node = map.allocate(0u8, b"hello", b"world").unwrap();
  /// map.link(unlinked_node).unwrap();
  ///
  /// let unlinked_node2 = map.allocate(0u8, b"hello", b"rust").unwrap();
  /// map.link(unlinked_node2).unwrap();
  ///
  /// let entry = map.get(0u8, b"hello").unwrap();
  /// assert_eq!(entry.value(), b"rust");
  /// ```
  #[inline]
  pub fn allocate<'a, 'b: 'a>(
    &'a self,
    key: &'b [u8],
    value: &'b [u8],
    trailer: T,
  ) -> Result<UnlinkedNode<'a, T>, Error> {
    self
      .0
      .allocate_at_height(MIN_VERSION, self.0.random_height(), key, value, trailer)
  }

  /// Allocates a new node with a given height in the [`SkipMap`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipMap::link`] or [`SkipMap::get_or_link`].
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::*;
  ///
  /// let map = SkipMap::new().unwrap();
  ///
  /// let random_height = map.random_height();
  ///
  /// let unlinked_node = map.allocate_at_height(0u8, random_height, b"hello", b"world").unwrap();
  /// map.link(unlinked_node).unwrap();
  ///
  /// let unlinked_node2 = map.allocate_at_height(0u8, random_height, b"hello", b"rust").unwrap();
  /// map.link(unlinked_node2).unwrap();
  ///
  /// let entry = map.get(0u8, b"hello").unwrap();
  /// assert_eq!(entry.value(), b"rust");
  /// ```
  pub fn allocate_at_height<'a, 'b: 'a>(
    &'a self,

    height: Height,
    key: &'b [u8],
    value: &'b [u8],
    trailer: T,
  ) -> Result<UnlinkedNode<'a, T>, Error> {
    self
      .0
      .allocate_at_height(MIN_VERSION, height, key, value, trailer)
  }

  /// Gets an [`EntryRef`] corresponding to the key or allocates a new node in the [`SkipMap`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipMap::link`] or [`SkipMap::get_or_link`].
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{*, tailed::SkipMap};
  ///
  /// let map = SkipMap::<Ttl>::new().unwrap();
  ///
  /// let unlinked_node = map.get_or_allocate(b"hello", b"world", Ttl::new(std::time::Duration::from_secs(60))).unwrap().unwrap_left();
  /// map.link(unlinked_node).unwrap();
  ///
  /// let entry = map.get_or_allocate(b"hello", b"rust", Ttl::new(std::time::Duration::from_secs(60))).unwrap().unwrap_right();
  /// assert_eq!(entry.value(), b"world");
  /// ```
  #[inline]
  pub fn get_or_allocate<'a, 'b: 'a>(
    &'a self,
    key: &'b [u8],
    value: &'b [u8],
    trailer: T,
  ) -> Result<Either<UnlinkedNode<'a, T>, EntryRef<'a, T>>, Error> {
    self
      .0
      .get_or_allocate_at_height(MIN_VERSION, self.0.random_height(), key, value, trailer)
  }

  /// Gets an [`EntryRef`] corresponding to the key or allocates a new node in the [`SkipMap`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipMap::link`] or [`SkipMap::get_or_link`].
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{*};
  ///
  /// let map = SkipMap::<Ttl>::new().unwrap();
  ///
  /// let random_height = map.random_height();
  ///
  /// let unlinked_node = map.get_or_allocate_at_height(random_height, b"hello", b"world", Ttl::new(std::time::Duration::from_secs(60))).unwrap().unwrap_left();
  /// map.link(unlinked_node).unwrap();
  ///
  /// let entry = map.get_or_allocate_at_height(random_height, b"hello", b"rust", Ttl::new(std::time::Duration::from_secs(60))).unwrap().unwrap_right();
  /// assert_eq!(entry.value(), b"world");
  /// ```
  pub fn get_or_allocate_at_height<'a, 'b: 'a>(
    &'a self,
    height: Height,
    key: &'b [u8],
    value: &'b [u8],
    trailer: T,
  ) -> Result<Either<UnlinkedNode<'a, T>, EntryRef<'a, T>>, Error> {
    self
      .0
      .get_or_allocate_at_height(MIN_VERSION, height, key, value, trailer)
  }

  /// Allocates a new node in the [`SkipMap`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipMap::link`] or [`SkipMap::get_or_link`].
  ///
  /// This method is useful when you want to insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{trailed::SkipMap, time::Ttl, ValueBuilder};
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
  /// struct PersonRef<'a> {
  ///   id: u32,
  ///   name: &'a str,
  /// }
  ///
  /// impl<'a> TryFrom<&'a [u8]> for PersonRef<'a> {
  ///   type Error = core::str::Utf8Error;
  ///
  ///   fn try_from(value: &'a [u8]) -> Result<Self, Self::Error> {
  ///     let id = u32::from_le_bytes(value[..4].try_into().unwrap());
  ///     let name = core::str::from_utf8(&value[4..])?;
  ///     Ok(PersonRef { id, name })
  ///   }
  /// }
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = SkipMap::<Ttl>::new().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let node = l.allocate_with_value_builder::<core::convert::Infallible>(b"alice", vb, Ttl::new(std::time::Duration::from_secs(60)))
  /// .unwrap();
  ///
  /// // do something else
  ///
  /// l.link(node).unwrap();
  ///
  /// let entry = l.get(b"alice").unwrap();
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 1);
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&2u32.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let node = l.allocate_with_value_builder::<core::convert::Infallible>(b"alice", vb, Ttl::new(std::time::Duration::from_secs(60))).unwrap();
  ///
  /// // do something else
  ///
  /// l.link(node).unwrap();
  ///
  /// let entry = l.get(b"alice").unwrap();
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 2);
  /// ```
  #[inline]
  pub fn allocate_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    trailer: T,
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<UnlinkedNode<'a, T>, Either<E, Error>> {
    self.0.allocate_at_height_with_value_builder(
      MIN_VERSION,
      self.random_height(),
      key,
      value_builder,
      trailer,
    )
  }

  /// Allocates a new node in the [`SkipMap`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipMap::link`] or [`SkipMap::get_or_link`].
  ///
  /// This method is useful when you want to insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{trailed::SkipMap, time::Ttl, ValueBuilder};
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
  /// struct PersonRef<'a> {
  ///   id: u32,
  ///   name: &'a str,
  /// }
  ///
  /// impl<'a> TryFrom<&'a [u8]> for PersonRef<'a> {
  ///   type Error = core::str::Utf8Error;
  ///
  ///   fn try_from(value: &'a [u8]) -> Result<Self, Self::Error> {
  ///     let id = u32::from_le_bytes(value[..4].try_into().unwrap());
  ///     let name = core::str::from_utf8(&value[4..])?;
  ///     Ok(PersonRef { id, name })
  ///   }
  /// }
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = SkipMap::<Ttl>::new().unwrap();
  ///
  /// let random_height = l.random_height();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let node = l.allocate_at_height_with_value_builder::<core::convert::Infallible>(random_height, b"alice", vb, Ttl::new(std::time::Duration::from_secs(60)))
  /// .unwrap();
  ///
  /// // do something else
  ///
  /// l.link(node).unwrap();
  ///
  /// let entry = l.get(b"alice").unwrap();
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 1);
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&2u32.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let node = l.allocate_at_height_with_value_builder::<core::convert::Infallible>(random_height, b"alice", vb, Ttl::new(std::time::Duration::from_secs(60))).unwrap();
  ///
  /// // do something else
  ///
  /// l.link(node).unwrap();
  ///
  /// let entry = l.get(b"alice").unwrap();
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 2);
  /// ```
  pub fn allocate_at_height_with_value_builder<'a, 'b: 'a, E>(
    &'a self,

    height: Height,
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<UnlinkedNode<'a, T>, Either<E, Error>> {
    self
      .0
      .allocate_at_height_with_value_builder(MIN_VERSION, height, key, value_builder, trailer)
  }

  /// Gets an [`EntryRef`] corresponding to the key or allocates a new node in the [`SkipMap`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipMap::link`] or [`SkipMap::get_or_link`].
  ///
  /// This method is useful when you want to insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// Allocates a new node in the [`SkipMap`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipMap::link`] or [`SkipMap::get_or_link`].
  ///
  /// This method is useful when you want to insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{trailed::SkipMap, time::Ttl, ValueBuilder};
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
  /// struct PersonRef<'a> {
  ///   id: u32,
  ///   name: &'a str,
  /// }
  ///
  /// impl<'a> TryFrom<&'a [u8]> for PersonRef<'a> {
  ///   type Error = core::str::Utf8Error;
  ///
  ///   fn try_from(value: &'a [u8]) -> Result<Self, Self::Error> {
  ///     let id = u32::from_le_bytes(value[..4].try_into().unwrap());
  ///     let name = core::str::from_utf8(&value[4..])?;
  ///     Ok(PersonRef { id, name })
  ///   }
  /// }
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = SkipMap::<Ttl>::new().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let node = l.get_or_allocate_with_value_builder::<core::convert::Infallible>(b"alice", vb, Ttl::new(std::time::Duration::from_secs(60)))
  /// .unwrap().unwrap_left();
  ///
  /// // do something else
  ///
  /// l.link(node).unwrap();
  ///
  /// let entry = l.get(b"alice").unwrap();
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 1);
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&2u32.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let entry = l.get_or_allocate_with_value_builder::<core::convert::Infallible>(b"alice", vb, Ttl::new(std::time::Duration::from_secs(60))).unwrap().unwrap_right();
  ///
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 1);
  /// ```
  #[inline]
  pub fn get_or_allocate_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Either<UnlinkedNode<'a, T>, EntryRef<'a, T>>, Either<E, Error>> {
    self.0.get_or_allocate_at_height_with_value_builder(
      MIN_VERSION,
      self.random_height(),
      key,
      value_builder,
      trailer,
    )
  }

  /// Gets an [`EntryRef`] corresponding to the key or allocates a new node in the [`SkipMap`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipMap::link`] or [`SkipMap::get_or_link`].
  ///
  /// This method is useful when you want to insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// Allocates a new node in the [`SkipMap`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipMap::link`] or [`SkipMap::get_or_link`].
  ///
  /// This method is useful when you want to insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{trailed::SkipMap, time::Ttl, ValueBuilder};
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
  /// struct PersonRef<'a> {
  ///   id: u32,
  ///   name: &'a str,
  /// }
  ///
  /// impl<'a> TryFrom<&'a [u8]> for PersonRef<'a> {
  ///   type Error = core::str::Utf8Error;
  ///
  ///   fn try_from(value: &'a [u8]) -> Result<Self, Self::Error> {
  ///     let id = u32::from_le_bytes(value[..4].try_into().unwrap());
  ///     let name = core::str::from_utf8(&value[4..])?;
  ///     Ok(PersonRef { id, name })
  ///   }
  /// }
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = SkipMap::<Ttl>::new().unwrap();
  ///
  /// let random_height = l.random_height();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let node = l.get_or_allocate_at_height_with_value_builder::<core::convert::Infallible>(random_height, b"alice", vb, Ttl::new(std::time::Duration::from_secs(60)))
  /// .unwrap().unwrap_left();
  ///
  /// // do something else
  ///
  /// l.link(node).unwrap();
  ///
  /// let entry = l.get(b"alice").unwrap();
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 1);
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&2u32.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let entry = l.get_or_allocate_at_height_with_value_builder::<core::convert::Infallible>(random_height, b"alice", vb, Ttl::new(std::time::Duration::from_secs(60))).unwrap().unwrap_right();
  ///
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 1);
  /// ```
  pub fn get_or_allocate_at_height_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    height: Height,
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Either<UnlinkedNode<'a, T>, EntryRef<'a, T>>, Either<E, Error>> {
    self.0.get_or_allocate_at_height_with_value_builder(
      MIN_VERSION,
      height,
      key,
      value_builder,
      trailer,
    )
  }

  /// Allocates a new node with the given key and value size in the [`SkipMap`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipMap::link`] or [`SkipMap::get_or_link`].
  ///
  /// This method is useful when you want to insert a key-value pair and you know the key size and value size but you do not have the key and value
  /// at this moment.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{trailed::SkipMap, time::Ttl, KeyBuilder, ValueBuilder};
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
  /// struct PersonRef<'a> {
  ///   id: u32,
  ///   name: &'a str,
  /// }
  ///
  /// impl<'a> TryFrom<&'a [u8]> for PersonRef<'a> {
  ///   type Error = core::str::Utf8Error;
  ///
  ///   fn try_from(value: &'a [u8]) -> Result<Self, Self::Error> {
  ///     let id = u32::from_le_bytes(value[..4].try_into().unwrap());
  ///     let name = core::str::from_utf8(&value[4..])?;
  ///     Ok(PersonRef { id, name })
  ///   }
  /// }
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
  /// let kb = KeyBuilder::new(b"alice", |mut key| {
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
  /// let node = l.allocate_with::<core::convert::Infallible>(kb, vb)
  /// .unwrap();
  ///
  /// // do something else
  ///
  /// l.link(node).unwrap();
  ///
  /// let entry = l.get(b"alice").unwrap();
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 1);
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&2u32.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let node = l.allocate_with::<core::convert::Infallible>(kb, vb)
  /// .unwrap();
  ///
  /// // do something else
  ///
  /// l.link(node).unwrap();
  ///
  /// let entry = l.get(b"alice").unwrap();
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 2);
  /// ```
  pub fn allocate_with_builders<'a, E>(
    &'a self,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<UnlinkedNode<'a, T>, Either<E, Error>> {
    self.0.allocate_at_height_with_builders(
      MIN_VERSION,
      self.random_height(),
      key_builder,
      value_builder,
      trailer,
    )
  }

  /// Allocates a new node with the given key and value size in the [`SkipMap`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipMap::link`] or [`SkipMap::get_or_link`].
  ///
  /// This method is useful when you want to insert a key-value pair and you know the key size and value size but you do not have the key and value
  /// at this moment.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{trailed::SkipMap, time::Ttl, u27};
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
  /// struct PersonRef<'a> {
  ///   id: u32,
  ///   name: &'a str,
  /// }
  ///
  /// impl<'a> TryFrom<&'a [u8]> for PersonRef<'a> {
  ///   type Error = core::str::Utf8Error;
  ///
  ///   fn try_from(value: &'a [u8]) -> Result<Self, Self::Error> {
  ///     let id = u32::from_le_bytes(value[..4].try_into().unwrap());
  ///     let name = core::str::from_utf8(&value[4..])?;
  ///     Ok(PersonRef { id, name })
  ///   }
  /// }
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = SkipMap::<Ttl>::new().unwrap();
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
  /// let node = l.allocate_at_height_with_builders::<core::convert::Infallible>(kb, vb, Ttl::new(std::time::Duration::from_secs(60)))
  /// .unwrap();
  ///
  /// // do something else
  ///
  /// l.link(node).unwrap();
  ///
  /// let entry = l.get(b"alice").unwrap();
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 1);
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&2u32.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let node = l.allocate_at_height_with_builders::<core::convert::Infallible>(kb, vb, Ttl::new(std::time::Duration::from_secs(60)))
  /// .unwrap();
  ///
  /// // do something else
  ///
  /// l.link(node).unwrap();
  ///
  /// let entry = l.get(b"alice").unwrap();
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 2);
  /// ```
  pub fn allocate_at_height_with_builders<'a, E>(
    &'a self,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<UnlinkedNode<'a, T>, Either<E, Error>> {
    self.0.allocate_at_height_with_builders(
      MIN_VERSION,
      height,
      key_builder,
      value_builder,
      trailer,
    )
  }

  /// Gets an [`EntryRef`] corresponding to the key or allocates a new node with the given key and value size in the [`SkipMap`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipMap::link`] or [`SkipMap::get_or_link`].
  ///
  /// This method is useful when you want to insert a key-value pair and you know the key size and value size but you do not have the key and value
  /// at this moment.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{trailed::SkipMap, time::Ttl, KeyBuilder, ValueBuilder};
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
  /// struct PersonRef<'a> {
  ///   id: u32,
  ///   name: &'a str,
  /// }
  ///
  /// impl<'a> TryFrom<&'a [u8]> for PersonRef<'a> {
  ///   type Error = core::str::Utf8Error;
  ///
  ///   fn try_from(value: &'a [u8]) -> Result<Self, Self::Error> {
  ///     let id = u32::from_le_bytes(value[..4].try_into().unwrap());
  ///     let name = core::str::from_utf8(&value[4..])?;
  ///     Ok(PersonRef { id, name })
  ///   }
  /// }
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = SkipMap::<Ttl>::new().unwrap();
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
  /// let node = l.get_or_allocate_with_builders::<core::convert::Infallible>(kb, vb, Ttl::new(std::time::Duration::from_secs(60)))
  /// .unwrap().unwrap_left();
  ///
  /// // do something else
  ///
  /// l.link(node).unwrap();
  ///
  /// let entry = l.get(b"alice").unwrap();
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 1);
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |mut key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&2u32.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let entry = l.get_or_allocate_with_builders::<core::convert::Infallible>(kb, vb, Ttl::new(std::time::Duration::from_secs(60)))
  /// .unwrap().unwrap_right();
  ///
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 1);
  /// ```
  pub fn get_or_allocate_with_builders<'a, E>(
    &'a self,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Either<UnlinkedNode<'a, T>, EntryRef<'a, T>>, Either<E, Error>> {
    self.0.get_or_allocate_at_height_builders(
      MIN_VERSION,
      self.random_height(),
      key_builder,
      value_builder,
      trailer,
    )
  }

  /// Gets an [`EntryRef`] corresponding to the key or allocates a new node with the given key and value size in the [`SkipMap`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipMap::link`] or [`SkipMap::get_or_link`].
  ///
  /// This method is useful when you want to insert a key-value pair and you know the key size and value size but you do not have the key and value
  /// at this moment.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{trailed::SkipMap, time::Ttl, KeyBuilder, ValueBuilder};
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
  /// struct PersonRef<'a> {
  ///   id: u32,
  ///   name: &'a str,
  /// }
  ///
  /// impl<'a> TryFrom<&'a [u8]> for PersonRef<'a> {
  ///   type Error = core::str::Utf8Error;
  ///
  ///   fn try_from(value: &'a [u8]) -> Result<Self, Self::Error> {
  ///     let id = u32::from_le_bytes(value[..4].try_into().unwrap());
  ///     let name = core::str::from_utf8(&value[4..])?;
  ///     Ok(PersonRef { id, name })
  ///   }
  /// }
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = SkipMap::<Ttl>::new().unwrap();
  /// let random_height = l.random_height();
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
  /// let node = l.get_or_allocate_at_height_builders::<core::convert::Infallible>(random_height, kb, vb, Ttl::new(std::time::Duration::from_secs(60)))
  /// .unwrap().unwrap_left();
  ///
  /// // do something else
  ///
  /// l.link(node).unwrap();
  ///
  /// let entry = l.get(b"alice").unwrap();
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 1);
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |mut key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&2u32.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let entry = l.get_or_allocate_at_height_builders::<core::convert::Infallible>(random_height, kb, vb, Ttl::new(std::time::Duration::from_secs(60)))
  /// .unwrap().unwrap_right();
  ///
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 1);
  /// ```
  pub fn get_or_allocate_at_height_builders<'a, E>(
    &'a self,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Either<UnlinkedNode<'a, T>, EntryRef<'a, T>>, Either<E, Error>> {
    self.0.get_or_allocate_at_height_builders(
      MIN_VERSION,
      height,
      key_builder,
      value_builder,
      trailer,
    )
  }

  /// Allocates a new node which is marked as removed in the [`SkipMap`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipMap::link`] or [`SkipMap::get_or_link`].
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::*;
  ///
  /// let map = SkipMap::u64<>::new().unwrap();
  ///
  /// map.insert(b"hello", b"world").unwrap();
  ///
  /// let unlinked_node = map.allocate_remove_entry(b"hello", Ttl::new(std::time::Duration::from_secs(60))).unwrap();
  ///
  /// // we can still get the hello entry, because of the node is not linked yet.
  ///
  /// let entry = map.get(b"hello").unwrap();
  /// assert_eq!(entry.value(), b"world");
  ///
  /// map.link(unlinked_node).unwrap();
  ///
  /// // now we cannot get the hello entry, because of the node is linked and marked as removed.
  /// let entry = map.get(b"hello");
  /// assert!(entry.is_none());
  /// ```
  pub fn allocate_remove_entry<'a, 'b: 'a>(
    &'a self,
    key: &'b [u8],
    trailer: T,
  ) -> Result<UnlinkedNode<'a, T>, Error> {
    self
      .0
      .allocate_remove_entry_at_height(MIN_VERSION, self.random_height(), key, trailer)
  }

  /// Allocates a new node which is marked as removed in the [`SkipMap`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipMap::link`] or [`SkipMap::get_or_link`].
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::*;
  ///
  /// let map = SkipMap::<Ttl>::new().unwrap();
  ///
  /// map.insert(b"hello", b"world").unwrap();
  ///
  /// let unlinked_node = map.allocate_remove_entry_at_height(map.random_height(), b"hello", Ttl::new(std::time::Duration::from_secs(60))).unwrap();
  ///
  /// // we can still get the hello entry, because of the node is not linked yet.
  ///
  /// let entry = map.get(b"hello").unwrap();
  /// assert_eq!(entry.value(), b"world");
  ///
  /// map.link(unlinked_node).unwrap();
  ///
  /// // now we cannot get the hello entry, because of the node is linked and marked as removed.
  /// let entry = map.get(b"hello");
  /// assert!(entry.is_none());
  /// ```
  #[inline]
  pub fn allocate_remove_entry_at_height<'a, 'b: 'a>(
    &'a self,
    height: Height,
    key: &'b [u8],
    trailer: T,
  ) -> Result<UnlinkedNode<'a, T>, Error> {
    self
      .0
      .allocate_remove_entry_at_height(MIN_VERSION, height, key, trailer)
  }

  /// Gets an [`EntryRef`] corresponding to the key or allocates a new node which is marked as removed in the [`SkipMap`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipMap::link`] or [`SkipMap::get_or_link`].
  ///
  /// # Example
  ///
  /// - If the key is already removed, it will return `Either::Right(None)`.
  ///
  /// ```rust
  /// use skl::*;
  /// use core::sync::atomic::Ordering;
  ///
  /// let map = SkipMap::<Ttl>::new().unwrap();
  ///
  /// map.insert(b"hello", b"world").unwrap();
  ///
  /// map.compare_remove(b"hello", Ordering::Relaxed, Ordering::Relaxed).unwrap();
  /// let unlinked_node = map.get_or_allocate_remove_entry(b"hello", Ttl::new(std::time::Duration::from_secs(60))).unwrap().unwrap_right();
  /// assert!(unlinked_node.is_none());
  /// ```
  ///
  /// - If the key is not removed, it will return `Either::Right(Some(EntryRef))`.
  ///
  /// ```rust
  /// use skl::*;
  ///
  /// let map = SkipMap::<Ttl>::new().unwrap();
  ///
  /// map.insert(0u8, b"hello", b"world").unwrap();
  ///
  /// let unlinked_node = map.get_or_allocate_remove_entry(b"hello", Ttl::new(std::time::Duration::from_secs(60))).unwrap().unwrap_right();
  /// assert_eq!(unlinked_node.unwrap().value(), b"world");
  /// ```
  ///
  /// - If the key does not exist, it will return `Either::Left(UnlinkedNode)`.
  ///
  /// ```rust
  /// use skl::*;
  ///
  /// let map = SkipMap::new().unwrap();
  ///
  /// let unlinked_node = map.get_or_allocate_remove_entry(b"hello", Ttl::new(std::time::Duration::from_secs(60))).unwrap().unwrap_left();
  ///
  /// assert_eq!(unlinked_node.key(), b"hello");
  /// assert!(unlinked_node.value().is_none());
  ///
  /// map.link(unlinked_node).unwrap();
  /// ```
  pub fn get_or_allocate_remove_entry<'a, 'b: 'a>(
    &'a self,

    key: &'b [u8],
    trailer: T,
  ) -> Result<Either<UnlinkedNode<'a, T>, Option<EntryRef<'a, T>>>, Error> {
    self
      .0
      .get_or_allocate_remove_entry_at_height(MIN_VERSION, self.random_height(), key, trailer)
  }

  /// Gets an [`EntryRef`] corresponding to the key or allocates a new node which is marked as removed in the [`SkipMap`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipMap::link`] or [`SkipMap::get_or_link`].
  ///
  /// # Example
  ///
  /// - If the key is already removed, it will return `Either::Right(None)`.
  ///
  /// ```rust
  /// use skl::*;
  /// use core::sync::atomic::Ordering;
  ///
  /// let map = SkipMap::new().unwrap();
  ///
  /// map.insert(0u8, b"hello", b"world").unwrap();
  ///
  /// map.compare_remove(0u8, b"hello", Ordering::Relaxed, Ordering::Relaxed).unwrap();
  /// let unlinked_node = map.get_or_allocate_remove_entry_at_height(map.random_height(), b"hello", Ttl::new(std::time::Duration::from_secs(60))).unwrap().unwrap_right();
  /// assert!(unlinked_node.is_none());
  /// ```
  ///
  /// - If the key is not removed, it will return `Either::Right(Some(EntryRef))`.
  ///
  /// ```rust
  /// use skl::*;
  ///
  /// let map = SkipMap::new().unwrap();
  ///
  /// map.insert(0u8, b"hello", b"world").unwrap();
  ///
  /// let unlinked_node = map.get_or_allocate_remove_entry_at_height(map.random_height(), b"hello", Ttl::new(std::time::Duration::from_secs(60))).unwrap().unwrap_right();
  /// assert_eq!(unlinked_node.unwrap().value(), b"world");
  /// ```
  ///
  /// - If the key does not exist, it will return `Either::Left(UnlinkedNode)`.
  ///
  /// ```rust
  /// use skl::*;
  ///
  /// let map = SkipMap::new().unwrap();
  ///
  /// let unlinked_node = map.get_or_allocate_remove_entry_at_height(map.random_height(), b"hello", Ttl::new(std::time::Duration::from_secs(60))).unwrap().unwrap_left();
  ///
  /// assert_eq!(unlinked_node.key(), b"hello");
  /// assert!(unlinked_node.value().is_none());
  ///
  /// map.link(unlinked_node).unwrap();
  /// ```
  pub fn get_or_allocate_remove_entry_at_height<'a, 'b: 'a>(
    &'a self,
    height: Height,
    key: &'b [u8],
    trailer: T,
  ) -> Result<Either<UnlinkedNode<'a, T>, Option<EntryRef<'a, T>>>, Error> {
    self
      .0
      .get_or_allocate_remove_entry_at_height(MIN_VERSION, height, key, trailer)
  }

  /// Allocates a new node which is marked as removed in the [`SkipMap`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipMap::link`] or [`SkipMap::get_or_link`].
  ///
  /// This method is useful when you want to remove a key and you know the key size but you do not have the key
  /// at this moment.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{trailed::SkipMap, time::Ttl, u27, KeyBuilder};
  ///
  /// let map = SkipMap::<Ttl>::new().unwrap();
  ///
  /// map.insert(0u8, b"hello", b"world").unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |mut key| {
  ///   key.write(b"hello").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let unlinked_node = map.allocate_remove_entry_builder::<core::convert::Infallible>(kb, Ttl::new(std::time::Duration::from_secs(60))).unwrap();
  ///
  /// // we can still get the hello entry, because of the node is not linked yet.
  /// let entry = map.get(0u8, b"hello").unwrap();
  ///
  /// assert_eq!(entry.value(), b"world");
  ///
  /// // do something else
  ///
  /// map.link(unlinked_node).unwrap();
  /// ```
  #[inline]
  pub fn allocate_remove_entry_with_builder<'a, E>(
    &'a self,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<UnlinkedNode<'a, T>, Either<E, Error>> {
    self.0.allocate_remove_entry_at_height_with_builder(
      MIN_VERSION,
      self.random_height(),
      key_builder,
      trailer,
    )
  }

  /// Allocates a new node which is marked as removed in the [`SkipMap`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipMap::link`] or [`SkipMap::get_or_link`].
  ///
  /// This method is useful when you want to remove a key and you know the key size but you do not have the key
  /// at this moment.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{trailed::SkipMap, time::Ttl, u27, KeyBuilder};
  ///
  /// let map = SkipMap::<Ttl>::new().unwrap();
  ///
  /// map.insert(0u8, b"hello", b"world").unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |mut key| {
  ///   key.write(b"hello").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let unlinked_node = map.allocate_remove_entry_at_height_with_builder::<core::convert::Infallible>(map.random_height(), kb, Ttl::new(std::time::Duration::from_secs(60))).unwrap();
  ///
  /// // we can still get the hello entry, because of the node is not linked yet.
  /// let entry = map.get(b"hello").unwrap();
  ///
  /// assert_eq!(entry.value(), b"world");
  ///
  /// // do something else
  ///
  /// map.link(unlinked_node).unwrap();
  /// ```
  pub fn allocate_remove_entry_at_height_with_builder<'a, E>(
    &'a self,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<UnlinkedNode<'a, T>, Either<E, Error>> {
    self
      .0
      .allocate_remove_entry_at_height_with_builder(MIN_VERSION, height, key_builder, trailer)
  }

  /// Gets an [`EntryRef`] corresponding to the key or allocates a new node which is marked as removed in the [`SkipMap`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipMap::link`] or [`SkipMap::get_or_link`].
  ///
  /// If the key is already removed, it will return `Either::Right(None)`.
  /// If the key is not removed, it will return `Either::Right(Some(EntryRef))`.
  /// If the key does not exist, it will return `Either::Left(UnlinkedNode)`.
  ///
  /// This method is useful when you want to remove a key and you know the key size but you do not have the key
  /// at this moment.
  ///
  /// # Example
  ///
  /// See examples in [`get_or_allocate_remove_entry`](SkipMap::get_or_allocate_remove_entry) and [`allocate_remove_entry_with_builder`](SkipMap::allocate_remove_entry_with_builder).
  #[inline]
  pub fn get_or_allocate_remove_entry_with_builder<'a, E>(
    &'a self,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Either<UnlinkedNode<'a, T>, Option<EntryRef<'a, T>>>, Either<E, Error>> {
    self.0.get_or_allocate_remove_entry_at_height_with_builder(
      MIN_VERSION,
      self.random_height(),
      key_builder,
      trailer,
    )
  }

  /// Gets an [`EntryRef`] corresponding to the key or allocates a new node which is marked as removed in the [`SkipMap`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipMap::link`] or [`SkipMap::get_or_link`].
  ///
  /// If the key is already removed, it will return `Either::Right(None)`.
  /// If the key is not removed, it will return `Either::Right(Some(EntryRef))`.
  /// If the key does not exist, it will return `Either::Left(UnlinkedNode)`.
  ///
  /// This method is useful when you want to remove a key and you know the key size but you do not have the key
  /// at this moment.
  ///
  /// # Example
  ///
  /// See examples in [`get_or_allocate_remove_entry_at_height`](SkipMap::get_or_allocate_remove_entry_at_height) and [`allocate_remove_entry_at_height_with_builder`](SkipMap::allocate_remove_entry_at_height_with_builder).
  pub fn get_or_allocate_remove_entry_at_height_with_builder<'a, E>(
    &'a self,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Either<UnlinkedNode<'a, T>, Option<EntryRef<'a, T>>>, Either<E, Error>> {
    self.0.get_or_allocate_remove_entry_at_height_with_builder(
      MIN_VERSION,
      height,
      key_builder,
      trailer,
    )
  }

  /// Links a node into the [`SkipMap`].
  ///
  /// Use this method to link a [`UnlinkedNode`] that was allocated through `allocate*` APIs.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::*;
  ///
  /// let map = SkipMap::new().unwrap();
  ///
  /// let unlinked_node = map.allocate(0u8, b"hello", b"world").unwrap();
  ///
  /// // do something else
  ///
  /// map.link(unlinked_node).unwrap();
  /// ```
  pub fn link<'a>(&'a self, node: UnlinkedNode<'a, T>) -> Result<Option<EntryRef<'a, T>>, Error> {
    self.0.link(node)
  }

  /// Gets an entry or links a node into the [`SkipMap`].
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::*;
  ///
  /// let map = SkipMap::new().unwrap();
  ///
  /// let unlinked_node = map.allocate(0u8, b"hello", b"world").unwrap();
  ///
  /// // do something else
  ///
  /// map.get_or_link(unlinked_node).unwrap();
  /// ```
  pub fn get_or_link<'a>(
    &'a self,
    node: UnlinkedNode<'a, T>,
  ) -> Result<Option<EntryRef<'a, T>>, Error> {
    self.0.get_or_link(node)
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
  ) -> Result<Option<EntryRef<'a, T>>, Error> {
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
  /// use skl::{trailed::SkipMap, Ascend, time::Ttl};
  ///
  /// let map = SkipMap::<Ascend, Ttl>::new().unwrap();
  ///
  /// let height = map.random_height();
  /// map.insert_at_height(height, b"hello", b"world", Ttl::new(std::time::Duration::from_secs(60))).unwrap();
  /// ```
  pub fn insert_at_height<'a, 'b: 'a>(
    &'a self,
    height: Height,
    key: &'b [u8],
    value: &'b [u8],
    trailer: T,
  ) -> Result<Option<EntryRef<'a, T>>, Error> {
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
  /// use skl::{trailed::SkipMap, ValueBuilder, Ascend, time::Ttl};
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
  /// let l = SkipMap::<Ascend, Ttl>::new().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// l.insert_with_value_builder::<core::convert::Infallible>(b"alice", vb, Ttl::new(std::time::Duration::from_secs(60)))
  /// .unwrap();
  /// ```
  #[inline]
  pub fn insert_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, T>>, Either<E, Error>> {
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
  /// use skl::{trailed::SkipMap, ValueBuilder, time::Ttl};
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
  /// let l = SkipMap::<Ascend, Ttl>::new().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.insert_at_height_with_value_builder::<core::convert::Infallible>(height, b"alice", vb, Ttl::new(std::time::Duration::from_secs(60)))
  /// .unwrap();
  /// ```
  pub fn insert_at_height_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    height: Height,
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, T>>, Either<E, Error>> {
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
  ) -> Result<Option<EntryRef<'a, T>>, Error> {
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
  ) -> Result<Option<EntryRef<'a, T>>, Error> {
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
  /// use skl::{trailed::SkipMap, ValueBuilder, Ascend, time::Ttl};
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
  /// let l = SkipMap::<Ascend, Ttl>::new().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  /// l.get_or_insert_with_value_builder::<core::convert::Infallible>(b"alice", vb, Ttl::new(std::time::Duration::from_secs(60)))
  /// .unwrap();
  /// ```
  #[inline]
  pub fn get_or_insert_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, T>>, Either<E, Error>> {
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
  /// use skl::{trailed::SkipMap, ValueBuilder, Ascend, time::Ttl};
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
  /// let l = SkipMap::<Ascend, Ttl>::new().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.get_or_insert_at_height_with_value_builder::<core::convert::Infallible>(height, b"alice", vb, Ttl::new(std::time::Duration::from_secs(60)))
  /// .unwrap();
  /// ```
  pub fn get_or_insert_at_height_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    height: Height,
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, T>>, Either<E, Error>> {
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
  /// use skl::{trailed::SkipMap, u27, KeyBuilder, ValueBuilder};
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
  /// l.insert_with_builders::<core::convert::Infallible>(kb, vb, Ttl::new(std::time::Duration::from_secs(60)))
  /// .unwrap();
  /// ```
  #[inline]
  pub fn insert_with_builders<'a, E>(
    &'a self,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, T>>, Either<E, Error>> {
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
  /// use skl::{trailed::SkipMap, KeyBuilder, ValueBuilder, Ascend, time::Ttl};
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
  /// let l = SkipMap::<Ttl>::new().unwrap();
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
  /// l.insert_at_height_with_builders::<core::convert::Infallible>(height, kb, vb, Ttl::new(std::time::Duration::from_secs(60)))
  /// .unwrap();
  /// ```
  pub fn insert_at_height_with_builders<'a, E>(
    &'a self,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, T>>, Either<E, Error>> {
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
  /// use skl::{trailed::SkipMap, KeyBuilder, ValueBuilder, Ascend, time::Ttl};
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
  /// let l = SkipMap::<Ascend, Ttl>::new().unwrap();
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
  /// l.get_or_insert_with_builders::<core::convert::Infallible>(kb, vb, Ttl::new(std::time::Duration::from_secs(60)))
  /// .unwrap();
  /// ```
  #[inline]
  pub fn get_or_insert_with_builders<'a, E>(
    &'a self,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, T>>, Either<E, Error>> {
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
  /// use skl::{trailed::SkipMap, KeyBuilder, ValueBuilder, Ascend, time::Ttl};
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
  /// let l = SkipMap::<Ascend, Ttl>::new().unwrap();
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
  /// l.get_or_insert_at_height_with_builders::<core::convert::Infallible>(height, kb, vb, Ttl::new(std::time::Duration::from_secs(60)))
  /// .unwrap();
  /// ```
  pub fn get_or_insert_at_height_with_builders<'a, E>(
    &'a self,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, T>>, Either<E, Error>> {
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
  ) -> Result<Option<EntryRef<'a, T>>, Error> {
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
  ) -> Result<Option<EntryRef<'a, T>>, Error> {
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
  ) -> Result<Option<EntryRef<'a, T>>, Error> {
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
  /// use skl::{trailed::SkipMap, Ascend, time::Ttl};
  ///
  /// let map = SkipMap::<Ascend, Ttl>::new().unwrap();
  ///
  /// map.insert(b"hello", b"world").unwrap();
  ///
  /// let height = map.random_height();
  /// map.get_or_remove_at_height(height, b"hello", Ttl::new(std::time::Duration::from_secs(60))).unwrap();
  /// ```
  pub fn get_or_remove_at_height<'a, 'b: 'a>(
    &'a self,
    height: Height,
    key: &'b [u8],
    trailer: T,
  ) -> Result<Option<EntryRef<'a, T>>, Error> {
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
  /// use skl::{trailed::SkipMap, KeyBuilder, Ascend, time::Ttl};
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
  /// let l = SkipMap::<Ascend, Ttl>::new().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |mut key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// });
  /// l.get_or_remove_with_builder::<core::convert::Infallible>(kb, Ttl::new(std::time::Duration::from_secs(60)))
  /// .unwrap();
  /// ```
  pub fn get_or_remove_with_builder<'a, 'b: 'a, E>(
    &'a self,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, T>>, Either<E, Error>> {
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
  /// use skl::{trailed::SkipMap, KeyBuilder, Ascend, time::Ttl};
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
  /// let l = SkipMap::<Ascend, Ttl>::new().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |mut key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// });
  /// let height = l.random_height();
  /// l.get_or_remove_at_height_with_builder::<core::convert::Infallible>(height, kb, Ttl::new(std::time::Duration::from_secs(60)))
  /// .unwrap();
  /// ```
  pub fn get_or_remove_at_height_with_builder<'a, 'b: 'a, E>(
    &'a self,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, T>>, Either<E, Error>> {
    self
      .0
      .get_or_remove_at_height_with_builder(MIN_VERSION, height, key_builder, trailer)
  }
}

impl<T: Trailer, C: Comparator> SkipMap<T, C> {
  /// Returns `true` if the key exists in the map.
  ///
  /// This method will return `false` if the entry is marked as removed. If you want to check if the key exists even if it is marked as removed,
  /// you can use [`contains_key_versioned`](SkipMap::contains_key_versioned).
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::SkipMap;
  ///
  /// let map = SkipMap::new().unwrap();
  ///
  /// map.insert(0u8, b"hello", b"world").unwrap();
  ///
  /// map.get_or_remove(b"hello").unwrap();
  ///
  /// assert!(!map.contains_key(b"hello"));
  /// assert!(map.contains_key_versioned(b"hello"));
  /// ```
  #[inline]
  pub fn contains_key<'a, 'b: 'a>(&'a self, key: &'b [u8]) -> bool {
    self.0.contains_key(MIN_VERSION, key)
  }

  /// Returns the first entry in the map.
  pub fn first(&self, version: Version) -> Option<EntryRef<'_, T>> {
    self.0.first(version)
  }

  /// Returns the last entry in the map.
  pub fn last(&self, version: Version) -> Option<EntryRef<'_, T>> {
    self.0.last(version)
  }

  /// Returns the value associated with the given key, if it exists.
  ///
  /// This method will return `None` if the entry is marked as removed. If you want to get the entry even if it is marked as removed,
  /// you can use [`get_versioned`](SkipMap::get_versioned).
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::SkipMap;
  ///
  /// let map = SkipMap::new().unwrap();
  ///
  /// map.insert(0u8, b"hello", b"world").unwrap();
  ///
  /// let ent = map.get(0u8, b"hello").unwrap();
  /// assert_eq!(ent.value(), b"world");
  ///
  /// map.get_or_remove(b"hello").unwrap();
  ///
  /// assert!(map.get(b"hello").is_none());
  /// ```
  pub fn get<'a, 'b: 'a>(&'a self, key: &'b [u8]) -> Option<EntryRef<'a, T>> {
    self.0.get(MIN_VERSION, key)
  }

  /// Returns an `EntryRef` pointing to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  pub fn upper_bound<'a, 'b: 'a>(&'a self, upper: Bound<&'b [u8]>) -> Option<EntryRef<'a, T>> {
    self.0.upper_bound(MIN_VERSION, upper)
  }

  /// Returns an `EntryRef` pointing to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  pub fn lower_bound<'a, 'b: 'a>(&'a self, lower: Bound<&'b [u8]>) -> Option<EntryRef<'a, T>> {
    self.0.lower_bound(MIN_VERSION, lower)
  }

  /// Returns a new iterator, this iterator will yield the latest version of all entries in the map less or equal to the given version.
  #[inline]
  pub fn iter(&self, version: Version) -> Iter<C, T> {
    self.0.iter(version)
  }

  /// Returns a iterator that within the range, this iterator will yield the latest version of all entries in the range less or equal to the given version.
  #[inline]
  pub fn range<'a, Q, R>(&'a self, range: R) -> Iter<'a, C, T, Q, R>
  where
    Q: ?Sized + Borrow<[u8]>,
    R: RangeBounds<Q> + 'a,
  {
    self.0.range(MIN_VERSION, range)
  }
}
