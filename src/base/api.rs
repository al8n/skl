use core::borrow::Borrow;

use rarena_allocator::ArenaOptions;

use super::*;

mod update;

type RemoveValueBuilder<E> =
  ValueBuilder<std::boxed::Box<dyn Fn(&mut VacantBuffer) -> Result<(), E>>>;

impl<A: Allocator> SkipList<A, Ascend> {
  /// Create a new skipmap with default options.
  ///
  /// **Note:** The capacity stands for how many memory allocated,
  /// it does not mean the skiplist can store `cap` entries.
  ///
  ///
  ///
  /// **What the difference between this method and [`SkipList::mmap_anon`]?**
  ///
  /// 1. This method will use an `AlignedVec` ensures we are working within Rust's memory safety guarantees.
  ///    Even if we are working with raw pointers with `Box::into_raw`,
  ///    the backend ARENA will reclaim the ownership of this memory by converting it back to a `Box`
  ///    when dropping the backend ARENA. Since `AlignedVec` uses heap memory, the data might be more cache-friendly,
  ///    especially if you're frequently accessing or modifying it.
  ///
  /// 2. Where as [`SkipList::mmap_anon`] will use mmap anonymous to require memory from the OS.
  ///    If you require very large contiguous memory regions, `mmap` might be more suitable because
  ///    it's more direct in requesting large chunks of memory from the OS.
  ///
  /// [`SkipList::mmap_anon`]: #method.mmap_anon
  #[allow(dead_code)]
  pub fn new(opts: Options) -> Result<Self, Error> {
    Self::with_comparator(opts, Ascend)
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
  #[allow(dead_code)]
  #[inline]
  pub unsafe fn map_mut<P: AsRef<std::path::Path>>(
    path: P,
    opts: Options,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> std::io::Result<Self> {
    Self::map_mut_with_comparator(path, opts, open_options, mmap_options, Ascend)
  }

  /// Open an exist file and mmap it to create skipmap.
  ///
  /// # Safety
  /// - If trying to reopens a skiplist, then the trailer type must be the same as the previous one.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[allow(dead_code)]
  pub unsafe fn map<P: AsRef<std::path::Path>>(
    path: P,
    opts: Options,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> std::io::Result<Self> {
    Self::map_with_comparator(path, opts, open_options, mmap_options, Ascend)
  }

  /// Create a new memory map backed skipmap with default options.
  ///
  /// **What the difference between this method and [`SkipList::new`]?**
  ///
  /// 1. This method will use mmap anonymous to require memory from the OS directly.
  ///    If you require very large contiguous memory regions, this method might be more suitable because
  ///    it's more direct in requesting large chunks of memory from the OS.
  ///
  /// 2. Where as [`SkipList::new`] will use an `AlignedVec` ensures we are working within Rust's memory safety guarantees.
  ///    Even if we are working with raw pointers with `Box::into_raw`,
  ///    the backend ARENA will reclaim the ownership of this memory by converting it back to a `Box`
  ///    when dropping the backend ARENA. Since `AlignedVec` uses heap memory, the data might be more cache-friendly,
  ///    especially if you're frequently accessing or modifying it.
  ///
  /// [`SkipList::new`]: #method.new
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[allow(dead_code)]
  #[inline]
  pub fn map_anon(opts: Options, mmap_options: MmapOptions) -> std::io::Result<Self> {
    Self::map_anon_with_comparator(opts, mmap_options, Ascend)
  }
}

impl<A: Allocator, C> SkipList<A, C> {
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
    self.arena.remove_on_drop(val);
  }

  /// Returns the offset of the data section in the `SkipList`.
  ///
  /// By default, `SkipList` will allocate meta, head node, and tail node in the ARENA,
  /// and the data section will be allocated after the tail node.
  ///
  /// This method will return the offset of the data section in the ARENA.
  #[inline]
  pub const fn data_offset(&self) -> usize {
    self.data_offset as usize
  }

  /// Returns the version number of the [`SkipList`].
  #[inline]
  pub fn version(&self) -> u16 {
    self.arena.magic_version()
  }

  /// Returns the magic version number of the [`SkipList`].
  ///
  /// This value can be used to check the compatibility for application using [`SkipList`].
  #[inline]
  pub fn magic_version(&self) -> u16 {
    self.meta().magic_version()
  }

  /// Returns the height of the highest tower within any of the nodes that
  /// have ever been allocated as part of this skiplist.
  #[inline]
  pub fn height(&self) -> u8 {
    self.meta().height()
  }

  /// Returns the number of remaining bytes can be allocated by the arena.
  #[inline]
  pub fn remaining(&self) -> usize {
    self.arena.remaining()
  }

  /// Returns how many bytes are discarded by the ARENA.
  #[inline]
  pub fn discarded(&self) -> u32 {
    self.arena.discarded()
  }

  /// Returns the number of bytes that have allocated from the arena.
  #[inline]
  pub fn allocated(&self) -> usize {
    self.arena.allocated()
  }

  /// Returns the capacity of the arena.
  #[inline]
  pub fn capacity(&self) -> usize {
    self.arena.capacity()
  }

  /// Returns the number of entries in the skipmap.
  #[inline]
  pub fn len(&self) -> usize {
    self.meta().len() as usize
  }

  /// Returns true if the skipmap is empty.
  #[inline]
  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }

  /// Gets the number of pointers to this `SkipList` similar to [`Arc::strong_count`](std::sync::Arc::strong_count).
  #[inline]
  pub fn refs(&self) -> usize {
    self.arena.refs()
  }

  /// Returns the maximum version of all entries in the map.
  #[inline]
  pub fn max_version(&self) -> u64 {
    self.meta().max_version()
  }

  /// Returns the minimum version of all entries in the map.
  #[inline]
  pub fn min_version(&self) -> u64 {
    self.meta().min_version()
  }

  /// Returns the comparator used to compare keys.
  #[inline]
  pub const fn comparator(&self) -> &C {
    &self.cmp
  }

  /// Returns a random generated height.
  ///
  /// This method is useful when you want to check if the underlying allocator can allocate a node.
  #[inline]
  pub fn random_height(&self) -> Height {
    random_height(self.opts.max_height())
  }

  /// Returns the estimated size of a node with the given height and key/value sizes.
  ///
  /// **Note**: The returned size is only an estimate and may not be accurate, which means that the actual size is less than or equal to the returned size.
  #[inline]
  pub fn estimated_node_size(height: Height, key_size: usize, value_size: usize) -> usize {
    let height: usize = height.into();
    7 // max padding
      + mem::size_of::<A::Node>()
      + mem::size_of::<<A::Node as Node>::Link>() * height
      + key_size
      + mem::align_of::<A::Trailer>() - 1 // max trailer padding
      + mem::size_of::<A::Trailer>()
      + value_size
  }

  /// Like [`SkipList::new`], but with a custom [`Comparator`].
  #[inline]
  pub fn with_comparator(opts: Options, cmp: C) -> Result<Self, Error> {
    let arena_opts = ArenaOptions::new()
      .with_capacity(opts.capacity())
      .with_maximum_alignment(mem::align_of::<A::Node>())
      .with_unify(opts.unify())
      .with_magic_version(CURRENT_VERSION)
      .with_freelist(opts.freelist())
      .with_reserved(opts.reserved());
    let arena = A::new(arena_opts, opts);
    Self::new_in(arena, cmp, opts)
  }

  /// Like [`SkipList::map_mut`], but with [`Options`] and a custom [`Comparator`].
  ///
  /// # Safety
  /// - If trying to reopens a skiplist, then the trailer type must be the same as the previous one.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub unsafe fn map_mut_with_comparator<P: AsRef<std::path::Path>>(
    path: P,
    opts: Options,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    cmp: C,
  ) -> std::io::Result<Self> {
    let alignment = mem::align_of::<A::Node>();
    let arena_opts = ArenaOptions::new()
      .with_maximum_alignment(alignment)
      .with_magic_version(CURRENT_VERSION)
      .with_freelist(opts.freelist())
      .with_reserved(opts.reserved());
    let arena = A::map_mut(path, arena_opts, open_options, mmap_options, opts)?;
    Self::new_in(arena, cmp, opts.with_unify(true))
      .map_err(invalid_data)
      .and_then(|map| {
        if map.magic_version() != opts.magic_version() {
          Err(bad_magic_version())
        } else if map.version() != CURRENT_VERSION {
          Err(bad_version())
        } else {
          // Lock the memory of first page to prevent it from being swapped out.
          #[cfg(not(windows))]
          unsafe {
            map
              .arena
              .mlock(0, map.arena.page_size().min(map.arena.capacity()))?;
          }

          Ok(map)
        }
      })
  }

  /// Like [`SkipList::map_mut`], but with [`Options`], a custom [`Comparator`] and a [`PathBuf`](std::path::PathBuf) builder.
  ///
  /// # Safety
  /// - If trying to reopens a skiplist, then the trailer type must be the same as the previous one.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub unsafe fn map_mut_with_comparator_and_path_builder<PB, E>(
    path_builder: PB,
    opts: Options,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    cmp: C,
  ) -> Result<Self, Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    let alignment = mem::align_of::<A::Node>();
    let arena_opts = ArenaOptions::new()
      .with_maximum_alignment(alignment)
      .with_magic_version(CURRENT_VERSION)
      .with_freelist(opts.freelist())
      .with_reserved(opts.reserved());
    let arena =
      A::map_mut_with_path_builder(path_builder, arena_opts, open_options, mmap_options, opts)?;
    Self::new_in(arena, cmp, opts.with_unify(true))
      .map_err(invalid_data)
      .and_then(|map| {
        if map.magic_version() != opts.magic_version() {
          Err(bad_magic_version())
        } else if map.version() != CURRENT_VERSION {
          Err(bad_version())
        } else {
          // Lock the memory of first page to prevent it from being swapped out.
          #[cfg(not(windows))]
          unsafe {
            map
              .arena
              .mlock(0, map.arena.page_size().min(map.arena.capacity()))?;
          }

          Ok(map)
        }
      })
      .map_err(Either::Right)
  }

  /// Like [`SkipList::map`], but with a custom [`Comparator`].
  ///
  /// # Safety
  /// - If trying to reopens a skiplist, then the trailer type must be the same as the previous one.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub unsafe fn map_with_comparator<P: AsRef<std::path::Path>>(
    path: P,
    opts: Options,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    cmp: C,
  ) -> std::io::Result<Self> {
    let opts = opts.with_unify(true);
    let magic_version = opts.magic_version();
    let arena_opts = ArenaOptions::new()
      .with_magic_version(CURRENT_VERSION)
      .with_reserved(opts.reserved());
    let arena = A::map(path, arena_opts, open_options, mmap_options, opts)?;
    Self::new_in(arena, cmp, opts)
      .map_err(invalid_data)
      .and_then(|map| {
        if map.magic_version() != magic_version {
          Err(bad_magic_version())
        } else if map.version() != CURRENT_VERSION {
          Err(bad_version())
        } else {
          // Lock the memory of first page to prevent it from being swapped out.
          #[cfg(not(windows))]
          unsafe {
            map
              .arena
              .mlock(0, map.arena.page_size().min(map.arena.capacity()))?;
          }

          Ok(map)
        }
      })
  }

  /// Like [`SkipList::map`], but with a custom [`Comparator`] and a [`PathBuf`](std::path::PathBuf) builder.
  ///
  /// # Safety
  /// - If trying to reopens a skiplist, then the trailer type must be the same as the previous one.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub unsafe fn map_with_comparator_and_path_builder<PB, E>(
    path_builder: PB,
    opts: Options,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    cmp: C,
  ) -> Result<Self, Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    let opts = opts.with_unify(true);

    let magic_version = opts.magic_version();
    let arena_opts = ArenaOptions::new()
      .with_magic_version(CURRENT_VERSION)
      .with_reserved(opts.reserved());
    let arena =
      A::map_with_path_builder(path_builder, arena_opts, open_options, mmap_options, opts)?;
    Self::new_in(arena, cmp, opts)
      .map_err(invalid_data)
      .and_then(|map| {
        if map.magic_version() != magic_version {
          Err(bad_magic_version())
        } else if map.version() != CURRENT_VERSION {
          Err(bad_version())
        } else {
          // Lock the memory of first page to prevent it from being swapped out.
          #[cfg(not(windows))]
          unsafe {
            map
              .arena
              .mlock(0, map.arena.page_size().min(map.arena.capacity()))?;
          }
          Ok(map)
        }
      })
      .map_err(Either::Right)
  }

  /// Like [`SkipList::map_anon`], but with a custom [`Comparator`].
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub fn map_anon_with_comparator(
    opts: Options,
    mmap_options: MmapOptions,
    cmp: C,
  ) -> std::io::Result<Self> {
    let alignment = mem::align_of::<A::Node>();
    let arena_opts = ArenaOptions::new()
      .with_maximum_alignment(alignment)
      .with_unify(opts.unify())
      .with_magic_version(CURRENT_VERSION)
      .with_reserved(opts.reserved());
    let arena = A::map_anon(arena_opts, mmap_options, opts)?;

    if cfg!(windows) {
      Self::new_in(arena, cmp, opts).map_err(invalid_data)
    } else {
      Self::new_in(arena, cmp, opts)
        .map_err(invalid_data)
        .and_then(|map| {
          // Lock the memory of first page to prevent it from being swapped out.
          #[cfg(not(windows))]
          unsafe {
            map
              .arena
              .mlock(0, map.arena.page_size().min(map.arena.capacity()))?;
          }
          Ok(map)
        })
    }
  }

  /// Clear the skiplist to empty and re-initialize.
  ///
  /// # Safety
  /// - The current pointers get from the ARENA cannot be used anymore after calling this method.
  /// - This method is not thread-safe.
  pub unsafe fn clear(&mut self) -> Result<(), Error> {
    self.arena.clear()?;

    let meta = if self.opts.unify() {
      self.arena.allocate_header(self.meta().magic_version())?
    } else {
      unsafe {
        let magic_version = self.meta().magic_version();
        let _ = Box::from_raw(self.meta.as_ptr());
        NonNull::new_unchecked(Box::into_raw(Box::new(<A::Header as Header>::new(
          magic_version,
        ))))
      }
    };

    self.meta = meta;

    let max_height: u8 = self.opts.max_height().into();
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

impl<A: Allocator, C: Comparator> SkipList<A, C> {
  /// Returns `true` if the key exists in the map.
  ///
  /// This method will return `false` if the entry is marked as removed. If you want to check if the key exists even if it is marked as removed,
  /// you can use [`contains_key_versioned`](SkipList::contains_key_versioned).
  #[inline]
  pub fn contains_key<'a, 'b: 'a>(&'a self, version: Version, key: &'b [u8]) -> bool {
    self.get(version, key).is_some()
  }

  /// Returns `true` if the key exists in the map, even if it is marked as removed.
  #[inline]
  pub fn contains_key_versioned<'a, 'b: 'a>(&'a self, version: Version, key: &'b [u8]) -> bool {
    self.get_versioned(version, key).is_some()
  }

  /// Returns the first entry in the map.
  pub fn first(&self, version: Version) -> Option<EntryRef<'_, A>> {
    self.iter(version).seek_lower_bound(Bound::Unbounded)
  }

  /// Returns the last entry in the map.
  pub fn last(&self, version: Version) -> Option<EntryRef<'_, A>> {
    self.iter(version).seek_upper_bound(Bound::Unbounded)
  }

  /// Returns the value associated with the given key, if it exists.
  ///
  /// This method will return `None` if the entry is marked as removed. If you want to get the entry even if it is marked as removed,
  /// you can use [`get_versioned`](SkipList::get_versioned).
  pub fn get<'a, 'b: 'a>(&'a self, version: Version, key: &'b [u8]) -> Option<EntryRef<'a, A>> {
    unsafe {
      let (n, eq) = self.find_near(version, key, false, true, true); // findLessOrEqual.

      let n = n?;
      let node = n.as_ref();
      let node_key = node.get_key(&self.arena);
      let (value, pointer) = node.get_value_and_trailer_with_pointer(&self.arena);
      if eq {
        return value.map(|_| {
          EntryRef(VersionedEntryRef::from_node_with_pointer(
            n,
            &self.arena,
            pointer,
          ))
        });
      }

      if !matches!(self.cmp.compare(key, node_key), cmp::Ordering::Equal) {
        return None;
      }

      if node.version() > version {
        return None;
      }

      value.map(|_| {
        EntryRef(VersionedEntryRef::from_node_with_pointer(
          n,
          &self.arena,
          pointer,
        ))
      })
    }
  }

  /// Returns the value associated with the given key, if it exists.
  ///
  /// The difference between `get` and `get_versioned` is that `get_versioned` will return the value even if the entry is removed.
  pub fn get_versioned<'a, 'b: 'a>(
    &'a self,
    version: Version,
    key: &'b [u8],
  ) -> Option<VersionedEntryRef<'a, A>> {
    unsafe {
      let (n, eq) = self.find_near(version, key, false, true, false); // findLessOrEqual.

      let n = n?;
      let node = n.as_ref();
      let node_key = node.get_key(&self.arena);
      let (_, pointer) = node.get_value_and_trailer_with_pointer(&self.arena);
      if eq {
        return Some(VersionedEntryRef::from_node_with_pointer(
          n,
          &self.arena,
          pointer,
        ));
      }

      if !matches!(self.cmp.compare(key, node_key), cmp::Ordering::Equal) {
        return None;
      }

      if node.version() > version {
        return None;
      }

      Some(VersionedEntryRef::from_node_with_pointer(
        n,
        &self.arena,
        pointer,
      ))
    }
  }

  /// Returns an `EntryRef` pointing to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  pub fn upper_bound<'a, 'b: 'a>(
    &'a self,
    version: Version,
    upper: Bound<&'b [u8]>,
  ) -> Option<EntryRef<'a, A>> {
    self.iter(version).seek_upper_bound(upper)
  }

  /// Returns an `EntryRef` pointing to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  pub fn lower_bound<'a, 'b: 'a>(
    &'a self,
    version: Version,
    lower: Bound<&'b [u8]>,
  ) -> Option<EntryRef<'a, A>> {
    self.iter(version).seek_lower_bound(lower)
  }

  /// Returns a new iterator, this iterator will yield the latest version of all entries in the map less or equal to the given version.
  #[inline]
  pub fn iter(&self, version: Version) -> iterator::Iter<A, C> {
    iterator::Iter::new(version, self)
  }

  /// Returns a new iterator, this iterator will yield all versions for all entries in the map less or equal to the given version.
  #[inline]
  pub fn iter_all_versions(&self, version: Version) -> iterator::AllVersionsIter<A, C> {
    iterator::AllVersionsIter::new(version, self, true)
  }

  /// Returns a iterator that within the range, this iterator will yield the latest version of all entries in the range less or equal to the given version.
  #[inline]
  pub fn range<'a, Q, R>(&'a self, version: Version, range: R) -> iterator::Iter<'a, A, C, Q, R>
  where
    Q: ?Sized + Borrow<[u8]>,
    R: RangeBounds<Q> + 'a,
  {
    iterator::Iter::range(version, self, range)
  }

  /// Returns a iterator that within the range, this iterator will yield all versions for all entries in the range less or equal to the given version.
  #[inline]
  pub fn range_all_versions<'a, Q, R>(
    &'a self,
    version: Version,
    range: R,
  ) -> iterator::AllVersionsIter<'a, A, C, Q, R>
  where
    Q: ?Sized + Borrow<[u8]>,
    R: RangeBounds<Q> + 'a,
  {
    iterator::AllVersionsIter::range(version, self, range, true)
  }
}
