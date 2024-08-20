use core::borrow::Borrow;

use rarena_allocator::{ArenaOptions, ArenaPosition};

use super::*;

mod allocate;
mod update;

macro_rules! builder {
  ($($name:ident($size:ident)),+ $(,)?) => {
    $(
      paste::paste! {
        #[doc = "A " [< $name: snake>] " builder for the [`SkipList`], which requires the " [< $name: snake>] " size for accurate allocation and a closure to build the " [< $name: snake>]]
        #[derive(Copy, Clone, Debug)]
        pub struct [< $name Builder >] <F> {
          size: $size,
          f: F,
        }

        impl<F> [< $name Builder >]<F> {
          #[doc = "Creates a new `" [<$name Builder>] "` with the given size and builder closure."]
          #[inline]
          pub const fn new<E>(size: $size, f: F) -> Self
          where
            F: for<'a> FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>,
          {
            Self { size, f }
          }

          #[doc = "Returns the required" [< $name: snake>] "size."]
          #[inline]
          pub const fn size(&self) -> $size {
            self.size
          }

          #[doc = "Returns the " [< $name: snake>] "builder closure."]
          #[inline]
          pub const fn builder(&self) -> &F {
            &self.f
          }

          /// Deconstructs the value builder into the size and the builder closure.
          #[inline]
          pub fn into_components(self) -> ($size, F) {
            (self.size, self.f)
          }
        }
      }
    )*
  };
}

builder!(Value(u32), Key(KeySize));

type RemoveValueBuilder<E> =
  ValueBuilder<std::boxed::Box<dyn Fn(&mut VacantBuffer) -> Result<(), E>>>;

impl<T> SkipList<Ascend, T> {
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
  pub fn new() -> Result<Self, Error> {
    Self::with_options(Options::new())
  }

  /// Like [`SkipList::new`], but with [`Options`].
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

  /// Like [`SkipList::map_mut`], but with [`Options`].
  ///
  /// # Safety
  /// - If trying to reopens a skiplist, then the trailer type must be the same as the previous one.
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
  /// - If trying to reopens a skiplist, then the trailer type must be the same as the previous one.
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
  pub fn map_anon(mmap_options: MmapOptions) -> std::io::Result<Self> {
    Self::map_anon_with_options_and_comparator(Options::new(), mmap_options, Ascend)
  }

  /// Like [`SkipList::map_anon`], but with [`Options`].
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn map_anon_with_options(opts: Options, mmap_options: MmapOptions) -> std::io::Result<Self> {
    Self::map_anon_with_options_and_comparator(opts, mmap_options, Ascend)
  }
}

impl<C, T> SkipList<C, T> {
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
  /// use skl::{SkipList, OpenOptions, MmapOptinos};
  ///
  /// const MAGIC_TEXT: u32 = u32::from_le_bytes(*b"al8n");
  ///
  /// struct Meta {
  ///   magic: u32,
  ///   version: u32,
  /// }
  ///
  /// let map = SkipList::map_mut(
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
    &self.arena
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
  pub const fn version(&self) -> u16 {
    self.arena.magic_version()
  }

  /// Returns the magic version number of the [`SkipList`].
  ///
  /// This value can be used to check the compatibility for application using [`SkipList`].
  #[inline]
  pub const fn magic_version(&self) -> u16 {
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

  /// Returns the number of bytes that have allocated from the arena.
  #[inline]
  pub fn allocated(&self) -> usize {
    self.arena.allocated()
  }

  /// Returns the capacity of the arena.
  #[inline]
  pub const fn capacity(&self) -> usize {
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

  /// Returns how many bytes are discarded by the ARENA.
  #[inline]
  pub fn discarded(&self) -> u32 {
    self.arena.discarded()
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
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::SkipList;
  ///
  /// let map = SkipList::<u64>::new().unwrap();
  /// let height = map.random_height();
  ///
  /// let needed = SkipList::<u64>::estimated_node_size(height, b"k1".len() as u32, b"k2".len() as u32);
  /// ```
  #[inline]
  pub fn random_height(&self) -> Height {
    random_height(self.opts.max_height())
  }

  /// Returns the estimated size of a node with the given height and key/value sizes.
  ///
  /// **Note**: The returned size is only an estimate and may not be accurate, which means that the actual size is less than or equal to the returned size.
  #[inline]
  pub fn estimated_node_size(height: Height, key_size: impl Into<usize>, value_size: u32) -> usize {
    let height: usize = height.into();
    7 // max padding
      + mem::size_of::<Node<T>>()
      + mem::size_of::<Link>() * height
      + key_size.into()
      + mem::align_of::<T>() - 1 // max trailer padding
      + mem::size_of::<T>()
      + value_size as usize
  }

  /// Like [`SkipList::new`], but with a custom [`Comparator`].
  #[inline]
  pub fn with_comparator(cmp: C) -> Result<Self, Error> {
    Self::with_options_and_comparator(Options::new(), cmp)
  }

  /// Like [`SkipList::new`], but with [`Options`] and a custom [`Comparator`].
  #[inline]
  pub fn with_options_and_comparator(opts: Options, cmp: C) -> Result<Self, Error> {
    let arena_opts = ArenaOptions::new()
      .with_capacity(opts.capacity())
      .with_maximum_alignment(Node::<T>::ALIGN as usize)
      .with_unify(opts.unify())
      .with_magic_version(CURRENT_VERSION)
      .with_freelist(opts.freelist());
    let arena = Arena::new(arena_opts);
    Self::new_in(arena, cmp, opts)
  }

  /// Like [`SkipList::map_mut`], but with a custom [`Comparator`].
  ///
  /// # Safety
  /// - If trying to reopens a skiplist, then the trailer type must be the same as the previous one.
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

  /// Like [`SkipList::map_mut`], but with [`Options`] and a custom [`Comparator`].
  ///
  /// # Safety
  /// - If trying to reopens a skiplist, then the trailer type must be the same as the previous one.
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
    let alignment = Node::<T>::ALIGN as usize;
    let arena_opts = ArenaOptions::new()
      .with_maximum_alignment(alignment)
      .with_magic_version(CURRENT_VERSION)
      .with_freelist(opts.freelist());
    let arena = Arena::map_mut(path, arena_opts, open_options, mmap_options)?;
    Self::new_in(arena, cmp, opts.with_unify(true))
      .map_err(invalid_data)
      .and_then(|map| {
        if map.magic_version() != opts.magic_version() {
          Err(bad_magic_version())
        } else if map.version() != CURRENT_VERSION {
          Err(bad_version())
        } else {
          // Lock the memory of first page to prevent it from being swapped out.
          unsafe {
            map.arena.mlock(0, map.arena.page_size().min(map.arena.capacity()))?;
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
  pub unsafe fn map_mut_with_options_and_comparator_and_path_builder<PB, E>(
    path_builder: PB,
    opts: Options,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    cmp: C,
  ) -> Result<Self, Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    let alignment = Node::<T>::ALIGN as usize;
    let arena_opts = ArenaOptions::new()
      .with_maximum_alignment(alignment)
      .with_magic_version(CURRENT_VERSION)
      .with_freelist(opts.freelist());
    let arena =
      Arena::map_mut_with_path_builder(path_builder, arena_opts, open_options, mmap_options)?;
    Self::new_in(arena, cmp, opts.with_unify(true))
      .map_err(invalid_data)
      .and_then(|map| {
        if map.magic_version() != opts.magic_version() {
          Err(bad_magic_version())
        } else if map.version() != CURRENT_VERSION {
          Err(bad_version())
        } else {
          // Lock the memory of first page to prevent it from being swapped out.
          unsafe {
            map.arena.mlock(0, map.arena.page_size().min(map.arena.capacity()))?;
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
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    cmp: C,
    magic_version: u16,
  ) -> std::io::Result<Self> {
    let arena = Arena::map(path, open_options, mmap_options, CURRENT_VERSION)?;
    Self::new_in(
      arena,
      cmp,
      Options::new()
        .with_unify(true)
        .with_magic_version(magic_version),
    )
    .map_err(invalid_data)
    .and_then(|map| {
      if map.magic_version() != magic_version {
        Err(bad_magic_version())
      } else if map.version() != CURRENT_VERSION {
        Err(bad_version())
      } else {
        // Lock the memory of first page to prevent it from being swapped out.
        unsafe {
          map.arena.mlock(0, map.arena.page_size().min(map.arena.capacity()))?;
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
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    cmp: C,
    magic_version: u16,
  ) -> Result<Self, Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    let arena =
      Arena::map_with_path_builder(path_builder, open_options, mmap_options, CURRENT_VERSION)?;
    Self::new_in(
      arena,
      cmp,
      Options::new()
        .with_unify(true)
        .with_magic_version(magic_version),
    )
    .map_err(invalid_data)
    .and_then(|map| {
      if map.magic_version() != magic_version {
        Err(bad_magic_version())
      } else if map.version() != CURRENT_VERSION {
        Err(bad_version())
      } else {
        // Lock the memory of first page to prevent it from being swapped out.
        unsafe {
          map.arena.mlock(0, map.arena.page_size().min(map.arena.capacity()))?;
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
  pub fn map_anon_with_comparator(mmap_options: MmapOptions, cmp: C) -> std::io::Result<Self> {
    Self::map_anon_with_options_and_comparator(Options::new(), mmap_options, cmp)
  }

  /// Like [`SkipList::map_anon`], but with [`Options`] and a custom [`Comparator`].
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub fn map_anon_with_options_and_comparator(
    opts: Options,
    mmap_options: MmapOptions,
    cmp: C,
  ) -> std::io::Result<Self> {
    let alignment = Node::<T>::ALIGN as usize;
    let arena_opts = ArenaOptions::new()
      .with_maximum_alignment(alignment)
      .with_unify(opts.unify())
      .with_magic_version(CURRENT_VERSION);
    let arena = Arena::map_anon(arena_opts, mmap_options)?;
    Self::new_in(arena, cmp, opts)
      .map_err(invalid_data)
      .and_then(|map| {
        // Lock the memory of first page to prevent it from being swapped out.
        unsafe {
          map.arena.mlock(0, map.arena.page_size().min(map.arena.capacity()))?;
        }
        Ok(map)
      })
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
  /// let map = SkipList::new().unwrap();
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
    self.arena.clear()?;

    let meta = if self.opts.unify() {
      Self::allocate_meta(&self.arena, self.meta().magic_version())?
    } else {
      unsafe {
        let magic_version = self.meta().magic_version();
        let _ = Box::from_raw(self.meta.as_ptr());
        NonNull::new_unchecked(Box::into_raw(Box::new(Meta::new(magic_version))))
      }
    };

    self.meta = meta;

    let max_height: u8 = self.opts.max_height().into();
    let head = Self::allocate_full_node(&self.arena, max_height)?;
    let tail = Self::allocate_full_node(&self.arena, max_height)?;

    // Safety:
    // We will always allocate enough space for the head node and the tail node.
    unsafe {
      // Link all head/tail levels together.
      for i in 0..(max_height as usize) {
        let head_link = head.tower(&self.arena, i);
        let tail_link = tail.tower(&self.arena, i);
        head_link.next_offset.store(tail.offset, Ordering::Relaxed);
        tail_link.prev_offset.store(head.offset, Ordering::Relaxed);
      }
    }

    self.head = head;
    self.tail = tail;
    Ok(())
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
  /// use skl::{SkipList, ArenaPosition};
  ///
  /// let map = SkipList::new().unwrap();
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
    self.arena.rewind(pos);
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

impl<T: Trailer, C: Comparator> SkipList<C, T> {
  /// Returns `true` if the key exists in the map.
  ///
  /// This method will return `false` if the entry is marked as removed. If you want to check if the key exists even if it is marked as removed,
  /// you can use [`contains_key_versioned`](SkipList::contains_key_versioned).
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::SkipList;
  ///
  /// let map = SkipList::new().unwrap();
  ///
  /// map.insert(0u8, b"hello", b"world").unwrap();
  ///
  /// map.get_or_remove(1u8, b"hello").unwrap();
  ///
  /// assert!(!map.contains_key(1u8, b"hello"));
  /// assert!(map.contains_key_versioned(1u8, b"hello"));
  /// ```
  #[inline]
  pub fn contains_key<'a, 'b: 'a>(&'a self, version: impl Into<Version>, key: &'b [u8]) -> bool {
    self.get(version, key).is_some()
  }

  /// Returns `true` if the key exists in the map, even if it is marked as removed.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::SkipList;
  ///
  /// let map = SkipList::new().unwrap();
  ///
  /// map.insert(0u8, b"hello", b"world").unwrap();
  ///
  /// map.get_or_remove(1u8, b"hello").unwrap();
  ///
  /// assert!(!map.contains_key(1u8, b"hello"));
  /// assert!(map.contains_key_versioned(1u8, b"hello"));
  /// ```
  #[inline]
  pub fn contains_key_versioned<'a, 'b: 'a>(
    &'a self,
    version: impl Into<Version>,
    key: &'b [u8],
  ) -> bool {
    self.get_versioned(version, key).is_some()
  }

  /// Returns the first entry in the map.
  pub fn first(&self, version: impl Into<Version>) -> Option<EntryRef<'_, T>> {
    self.iter(version).seek_lower_bound(Bound::Unbounded)
  }

  /// Returns the last entry in the map.
  pub fn last(&self, version: impl Into<Version>) -> Option<EntryRef<'_, T>> {
    self.iter(version).seek_upper_bound(Bound::Unbounded)
  }

  /// Returns the value associated with the given key, if it exists.
  ///
  /// This method will return `None` if the entry is marked as removed. If you want to get the entry even if it is marked as removed,
  /// you can use [`get_versioned`](SkipList::get_versioned).
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::SkipList;
  ///
  /// let map = SkipList::new().unwrap();
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
  pub fn get<'a, 'b: 'a>(
    &'a self,
    version: impl Into<Version>,
    key: &'b [u8],
  ) -> Option<EntryRef<'a, T>> {
    let version = version.into();
    unsafe {
      let (n, eq) = self.find_near(version, key, false, true); // findLessOrEqual.

      let n = n?;
      let node = n.as_ref();
      let node_key = node.get_key(&self.arena);
      let (_, value, pointer) = node.get_value_and_trailer_with_pointer(&self.arena);
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
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::SkipList;
  ///
  /// let map = SkipList::new().unwrap();
  ///
  /// map.insert(0u8, b"hello", b"world").unwrap();
  ///
  /// map.get_or_remove(1u8, b"hello").unwrap();
  ///
  /// assert!(map.get(1u8, b"hello").is_none());
  ///
  /// let ent = map.get_versioned(1u8, b"hello").unwrap();
  /// // value is None because the entry is marked as removed.
  /// assert!(ent.value().is_none());
  /// ```
  pub fn get_versioned<'a, 'b: 'a>(
    &'a self,
    version: impl Into<Version>,
    key: &'b [u8],
  ) -> Option<VersionedEntryRef<'a, T>> {
    let version = version.into();
    unsafe {
      let (n, eq) = self.find_near(version, key, false, true); // findLessOrEqual.

      let n = n?;
      let node = n.as_ref();
      let node_key = node.get_key(&self.arena);
      let (_, _, pointer) = node.get_value_and_trailer_with_pointer(&self.arena);
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
    version: impl Into<Version>,
    upper: Bound<&'b [u8]>,
  ) -> Option<EntryRef<'a, T>> {
    self.iter(version).seek_upper_bound(upper)
  }

  /// Returns an `EntryRef` pointing to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  pub fn lower_bound<'a, 'b: 'a>(
    &'a self,
    version: impl Into<Version>,
    lower: Bound<&'b [u8]>,
  ) -> Option<EntryRef<'a, T>> {
    self.iter(version).seek_lower_bound(lower)
  }

  /// Returns a new iterator, this iterator will yield the latest version of all entries in the map less or equal to the given version.
  #[inline]
  pub fn iter(&self, version: impl Into<Version>) -> iterator::Iter<C, T> {
    iterator::Iter::new(version.into(), self)
  }

  /// Returns a new iterator, this iterator will yield all versions for all entries in the map less or equal to the given version.
  #[inline]
  pub fn iter_all_versions(&self, version: impl Into<Version>) -> iterator::AllVersionsIter<C, T> {
    iterator::AllVersionsIter::new(version.into(), self, true)
  }

  /// Returns a iterator that within the range, this iterator will yield the latest version of all entries in the range less or equal to the given version.
  #[inline]
  pub fn range<'a, Q, R>(
    &'a self,
    version: impl Into<Version>,
    range: R,
  ) -> iterator::Iter<'a, C, T, Q, R>
  where
    Q: ?Sized + Borrow<[u8]>,
    R: RangeBounds<Q> + 'a,
  {
    iterator::Iter::range(version.into(), self, range)
  }

  /// Returns a iterator that within the range, this iterator will yield all versions for all entries in the range less or equal to the given version.
  #[inline]
  pub fn range_all_versions<'a, Q, R>(
    &'a self,
    version: impl Into<Version>,
    range: R,
  ) -> iterator::AllVersionsIter<'a, C, T, Q, R>
  where
    Q: ?Sized + Borrow<[u8]>,
    R: RangeBounds<Q> + 'a,
  {
    iterator::AllVersionsIter::range(version.into(), self, range, true)
  }
}
