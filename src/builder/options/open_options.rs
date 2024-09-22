use core::mem;

use dbutils::Comparator;
use either::Either;

#[cfg(not(windows))]
use rarena_allocator::Allocator;

use super::{super::Builder, Options, CURRENT_VERSION};
use crate::{
  allocator::Sealed,
  error::{bad_magic_version, bad_version, invalid_data},
  traits::Arena,
};

impl<C: Comparator> Builder<C> {
  /// Create a new map which is backed by a anonymous memory map.
  ///
  /// **What the difference between this method and [`Builder::alloc`]?**
  ///
  /// 1. This method will use mmap anonymous to require memory from the OS directly.
  ///    If you require very large contiguous memory regions, this method might be more suitable because
  ///    it's more direct in requesting large chunks of memory from the OS.
  ///
  /// 2. Where as [`Builder::alloc`] will use an `AlignedVec` ensures we are working within Rust's memory safety guarantees.
  ///    Even if we are working with raw pointers with `Box::into_raw`,
  ///    the backend ARENA will reclaim the ownership of this memory by converting it back to a `Box`
  ///    when dropping the backend ARENA. Since `AlignedVec` uses heap memory, the data might be more cache-friendly,
  ///    especially if you're frequently accessing or modifying it.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{full::sync, trailed::unsync, Builder};
  ///
  /// // Create a sync skipmap which supports both trailer and version.
  /// let map = Builder::new().with_capacity(1024).map_anon::<sync::SkipMap>().unwrap();
  ///
  /// // Create a unsync skipmap which supports trailer.
  /// let arena = Builder::new().with_capacity(1024).map_anon::<unsync::SkipMap>().unwrap();
  /// ```
  ///
  /// [`Builder::alloc`]: #method.alloc
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub fn map_anon<T: Arena<Comparator = C>>(self) -> std::io::Result<T> {
    let Self { opts, cmp } = self;

    let node_align = mem::align_of::<<T::Allocator as Sealed>::Node>();
    let trailer_align = mem::align_of::<<T::Allocator as Sealed>::Trailer>();

    #[allow(clippy::bind_instead_of_map)]
    opts
      .to_arena_options()
      .with_maximum_alignment(node_align.max(trailer_align))
      .map_anon::<<T::Allocator as Sealed>::Allocator>()
      .map_err(Into::into)
      .and_then(|arena| {
        T::construct(arena, opts, cmp, false)
          .map_err(invalid_data)
          .and_then(|map| {
            // Lock the memory of first page to prevent it from being swapped out.
            #[cfg(not(windows))]
            unsafe {
              let arena = map.allocator();
              arena.mlock(0, arena.page_size().min(arena.capacity()))?;
            }
            Ok(map)
          })
      })
  }

  /// Opens a read-only map which backed by file-backed memory map.
  ///
  /// ## Safety
  /// - If `T` is a `TrailedMap`, then trailer type must be the same as the one used to create the map.
  /// - The `C` must be the same as the one used to create the map.
  /// - All file-backed memory map constructors are marked `unsafe` because of the potential for
  ///   *Undefined Behavior* (UB) using the map if the underlying file is subsequently modified, in or
  ///   out of process. Applications must consider the risk and take appropriate precautions when
  ///   using file-backed maps. Solutions such as file permissions, locks or process-private (e.g.
  ///   unlinked) files exist but are platform specific and limited.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub unsafe fn map<T: Arena<Comparator = C>, P: AsRef<std::path::Path>>(
    self,
    path: P,
  ) -> std::io::Result<T> {
    self
      .map_with_path_builder::<T, _, ()>(|| Ok(path.as_ref().to_path_buf()))
      .map_err(Either::unwrap_right)
  }

  /// Opens a read-only map which backed by file-backed memory map with a path builder.
  ///
  /// ## Safety
  /// - If `T` is a `TrailedMap`, then trailer type must be the same as the one used to create the map.
  /// - The `C` must be the same as the one used to create the map.
  /// - All file-backed memory map constructors are marked `unsafe` because of the potential for
  ///   *Undefined Behavior* (UB) using the map if the underlying file is subsequently modified, in or
  ///   out of process. Applications must consider the risk and take appropriate precautions when
  ///   using file-backed maps. Solutions such as file permissions, locks or process-private (e.g.
  ///   unlinked) files exist but are platform specific and limited.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub unsafe fn map_with_path_builder<T, PB, E>(
    self,
    path_builder: PB,
  ) -> Result<T, Either<E, std::io::Error>>
  where
    T: Arena<Comparator = C>,
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    let Self { opts, cmp } = self;

    let node_align = mem::align_of::<<T::Allocator as Sealed>::Node>();
    let trailer_align = mem::align_of::<<T::Allocator as Sealed>::Trailer>();
    let magic_version = opts.magic_version();

    #[allow(clippy::bind_instead_of_map)]
    opts
      .to_arena_options()
      .with_maximum_alignment(node_align.max(trailer_align))
      .with_unify(true)
      .map_with_path_builder::<<T::Allocator as Sealed>::Allocator, _, _>(path_builder)
      .and_then(|arena| {
        T::construct(arena, opts, cmp, true)
          .map_err(invalid_data)
          .and_then(|map| {
            if Arena::magic_version(&map) != magic_version {
              Err(bad_magic_version())
            } else if map.version() != CURRENT_VERSION {
              Err(bad_version())
            } else {
              // Lock the memory of first page to prevent it from being swapped out.
              #[cfg(not(windows))]
              unsafe {
                let allocator = map.allocator();
                allocator.mlock(0, allocator.page_size().min(allocator.capacity()))?;
              }

              Ok(map)
            }
          })
          .map_err(Either::Right)
      })
  }

  /// Creates a new map or reopens a map which backed by a file backed memory map.
  ///
  /// ## Safety
  ///
  /// - If trying to reopen a map and `T` is a `TrailedMap`, then trailer type must be the same as the one used to create the map.
  /// - If trying to reopen a map, the `C` must be the same as the one used to create the map.
  /// - All file-backed memory map constructors are marked `unsafe` because of the potential for
  ///   *Undefined Behavior* (UB) using the map if the underlying file is subsequently modified, in or
  ///   out of process. Applications must consider the risk and take appropriate precautions when
  ///   using file-backed maps. Solutions such as file permissions, locks or process-private (e.g.
  ///   unlinked) files exist but are platform specific and limited.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub unsafe fn map_mut<T, P: AsRef<std::path::Path>>(self, path: P) -> std::io::Result<T>
  where
    T: Arena<Comparator = C>,
  {
    self
      .map_mut_with_path_builder::<T, _, ()>(|| Ok(path.as_ref().to_path_buf()))
      .map_err(Either::unwrap_right)
  }

  /// Creates a new map or reopens a map which backed by a file backed memory map with path builder.
  ///
  /// # Safety
  /// - If trying to reopen a map and `T` is a `TrailedMap`, then trailer type must be the same as the one used to create the map.
  /// - If trying to reopen a map, the `C` must be the same as the one used to create the map.
  /// - All file-backed memory map constructors are marked `unsafe` because of the potential for
  ///   *Undefined Behavior* (UB) using the map if the underlying file is subsequently modified, in or
  ///   out of process. Applications must consider the risk and take appropriate precautions when
  ///   using file-backed maps. Solutions such as file permissions, locks or process-private (e.g.
  ///   unlinked) files exist but are platform specific and limited.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub unsafe fn map_mut_with_path_builder<T, PB, E>(
    self,
    path_builder: PB,
  ) -> Result<T, Either<E, std::io::Error>>
  where
    T: Arena<Comparator = C>,
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    let Self { opts, cmp } = self;

    let node_align = mem::align_of::<<T::Allocator as Sealed>::Node>();
    let trailer_align = mem::align_of::<<T::Allocator as Sealed>::Trailer>();
    let magic_version = opts.magic_version();
    let path = path_builder().map_err(Either::Left)?;
    let exist = path.exists();

    #[allow(clippy::bind_instead_of_map)]
    opts
      .to_arena_options()
      .with_maximum_alignment(node_align.max(trailer_align))
      .with_unify(true)
      .map_mut::<<T::Allocator as Sealed>::Allocator, _>(path)
      .map_err(Either::Right)
      .and_then(|arena| {
        T::construct(arena, opts, cmp, exist)
          .map_err(invalid_data)
          .and_then(|map| {
            if Arena::magic_version(&map) != magic_version {
              Err(bad_magic_version())
            } else if map.version() != CURRENT_VERSION {
              Err(bad_version())
            } else {
              // Lock the memory of first page to prevent it from being swapped out.
              #[cfg(not(windows))]
              unsafe {
                let allocator = map.allocator();
                allocator.mlock(0, allocator.page_size().min(allocator.capacity()))?;
              }

              Ok(map)
            }
          })
          .map_err(Either::Right)
      })
  }
}

impl<C> Builder<C> {
  /// Sets the option for read access.
  ///
  /// This option, when true, will indicate that the file should be
  /// `read`-able if opened.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Builder;
  ///
  /// let opts = Builder::new().with_read(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_read(mut self, read: bool) -> Self {
    self.opts.read = read;
    self
  }

  /// Sets the option for write access.
  ///
  /// This option, when true, will indicate that the file should be
  /// `write`-able if opened.
  ///
  /// If the file already exists, any write calls on it will overwrite its
  /// contents, without truncating it.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Builder;
  ///
  /// let opts = Builder::new().with_write(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_write(mut self, write: bool) -> Self {
    self.opts.write = write;
    self
  }

  /// Sets the option for the append mode.
  ///
  /// This option, when true, means that writes will append to a file instead
  /// of overwriting previous contents.
  /// Note that setting `.write(true).append(true)` has the same effect as
  /// setting only `.append(true)`.
  ///
  /// For most filesystems, the operating system guarantees that all writes are
  /// atomic: no writes get mangled because another process writes at the same
  /// time.
  ///
  /// One maybe obvious note when using append-mode: make sure that all data
  /// that belongs together is written to the file in one operation. This
  /// can be done by concatenating strings before passing them to [`write()`],
  /// or using a buffered writer (with a buffer of adequate size),
  /// and calling [`flush()`] when the message is complete.
  ///
  /// If a file is opened with both read and append access, beware that after
  /// opening, and after every write, the position for reading may be set at the
  /// end of the file. So, before writing, save the current position (using
  /// <code>[seek]\([SeekFrom](std::io::SeekFrom)::[Current]\(opts))</code>), and restore it before the next read.
  ///
  /// ## Note
  ///
  /// This function doesn't create the file if it doesn't exist. Use the
  /// [`Options::with_create`] method to do so.
  ///
  /// [`write()`]: std::io::Write::write "io::Write::write"
  /// [`flush()`]: std::io::Write::flush "io::Write::flush"
  /// [seek]: std::io::Seek::seek "io::Seek::seek"
  /// [Current]: std::io::SeekFrom::Current "io::SeekFrom::Current"
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Builder;
  ///
  /// let opts = Builder::new().with_append(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_append(mut self, append: bool) -> Self {
    self.opts.write = true;
    self.opts.append = append;
    self
  }

  /// Sets the option for truncating a previous file.
  ///
  /// If a file is successfully opened with this option set it will truncate
  /// the file to opts length if it already exists.
  ///
  /// The file must be opened with write access for truncate to work.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Builder;
  ///
  /// let opts = Builder::new().with_write(true).with_truncate(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_truncate(mut self, truncate: bool) -> Self {
    self.opts.truncate = truncate;
    self.opts.write = true;
    self
  }

  /// Sets the option to create a new file, or open it if it already exists.
  /// If the file does not exist, it is created and set the lenght of the file to the given size.
  ///
  /// In order for the file to be created, [`Options::with_write`] or
  /// [`Options::with_append`] access must be used.
  ///
  /// See also [`std::fs::write()`][std::fs::write] for a simple function to
  /// create a file with some given data.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Builder;
  ///
  /// let opts = Builder::new().with_write(true).with_create(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_create(mut self, val: bool) -> Self {
    self.opts.create = val;
    self
  }

  /// Sets the option to create a new file and set the file length to the given value, failing if it already exists.
  ///
  /// No file is allowed to exist at the target location, also no (dangling) symlink. In this
  /// way, if the call succeeds, the file returned is guaranteed to be new.
  ///
  /// This option is useful because it is atomic. Otherwise between checking
  /// whether a file exists and creating a new one, the file may have been
  /// created by another process (a TOCTOU race condition / attack).
  ///
  /// If `.with_create_new(true)` is set, [`.with_create()`](Options::with_create) and [`.with_truncate()`](Options::with_truncate) are
  /// ignored.
  ///
  /// The file must be opened with write or append access in order to create
  /// a new file.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Builder;
  ///
  /// let file = Builder::new()
  ///   .with_write(true)
  ///   .with_create_new(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_create_new(mut self, val: bool) -> Self {
    self.opts.create_new = val;
    self
  }

  /// Configures the memory map to start at byte `offset` from the beginning of the file.
  ///
  /// This option has no effect on anonymous memory maps or vec backed [`Allocator`](crate::Allocator).
  ///
  /// By default, the offset is 0.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::Builder;
  ///
  /// let opts = Builder::new().with_offset(30);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_offset(mut self, offset: u64) -> Self {
    self.opts.offset = offset;
    self
  }

  /// Configures the anonymous memory map to be suitable for a process or thread stack.
  ///
  /// This option corresponds to the `MAP_STACK` flag on Linux. It has no effect on Windows.
  ///
  /// This option has no effect on file-backed memory maps and vec backed [`Allocator`](crate::Allocator).
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::Builder;
  ///
  /// let stack = Builder::new().with_stack(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_stack(mut self, stack: bool) -> Self {
    self.opts.stack = stack;
    self
  }

  /// Configures the anonymous memory map to be allocated using huge pages.
  ///
  /// This option corresponds to the `MAP_HUGETLB` flag on Linux. It has no effect on Windows.
  ///
  /// The size of the requested page can be specified in page bits. If not provided, the system
  /// default is requested. The requested length should be a multiple of this, or the mapping
  /// will fail.
  ///
  /// This option has no effect on file-backed memory maps and vec backed [`Allocator`](crate::Allocator).
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::Builder;
  ///
  /// let stack = Builder::new().with_huge(Some(8));
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_huge(mut self, page_bits: Option<u8>) -> Self {
    self.opts.huge = page_bits;
    self
  }

  /// Populate (prefault) page tables for a mapping.
  ///
  /// For a file mapping, this causes read-ahead on the file. This will help to reduce blocking on page faults later.
  ///
  /// This option corresponds to the `MAP_POPULATE` flag on Linux. It has no effect on Windows.
  ///
  /// This option has no effect on vec backed [`Allocator`](crate::Allocator).
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::Builder;
  ///
  /// let opts = Builder::new().with_populate(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_populate(mut self, populate: bool) -> Self {
    self.opts.populate = populate;
    self
  }
}

impl<C> Builder<C> {
  /// Returns `true` if the file should be opened with read access.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Builder;
  ///
  /// let opts = Builder::new().with_read(true);
  /// assert_eq!(opts.read(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn read(&self) -> bool {
    self.opts.read
  }

  /// Returns `true` if the file should be opened with write access.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Builder;
  ///
  /// let opts = Builder::new().with_write(true);
  /// assert_eq!(opts.write(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn write(&self) -> bool {
    self.opts.write
  }

  /// Returns `true` if the file should be opened with append access.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Builder;
  ///
  /// let opts = Builder::new().with_append(true);
  /// assert_eq!(opts.append(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn append(&self) -> bool {
    self.opts.append
  }

  /// Returns `true` if the file should be opened with truncate access.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Builder;
  ///
  /// let opts = Builder::new().with_truncate(true);
  /// assert_eq!(opts.truncate(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn truncate(&self) -> bool {
    self.opts.truncate
  }

  /// Returns `true` if the file should be created if it does not exist.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Builder;
  ///
  /// let opts = Builder::new().with_create(true);
  /// assert_eq!(opts.create(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn create(&self) -> bool {
    self.opts.create
  }

  /// Returns `true` if the file should be created if it does not exist and fail if it does.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Builder;
  ///
  /// let opts = Builder::new().with_create_new(true);
  /// assert_eq!(opts.create_new(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn create_new(&self) -> bool {
    self.opts.create_new
  }

  /// Returns the offset of the memory map.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Builder;
  ///
  /// let opts = Builder::new().with_offset(30);
  /// assert_eq!(opts.offset(), 30);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn offset(&self) -> u64 {
    self.opts.offset
  }

  /// Returns `true` if the memory map should be suitable for a process or thread stack.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Builder;
  ///
  /// let opts = Builder::new().with_stack(true);
  /// assert_eq!(opts.stack(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn stack(&self) -> bool {
    self.opts.stack
  }

  /// Returns the page bits of the memory map.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Builder;
  ///
  /// let opts = Builder::new().with_huge(Some(8));
  /// assert_eq!(opts.huge(), Some(8));
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn huge(&self) -> Option<u8> {
    self.opts.huge
  }

  /// Returns `true` if the memory map should populate (prefault) page tables for a mapping.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Builder;
  ///
  /// let opts = Builder::new().with_populate(true);
  /// assert_eq!(opts.populate(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn populate(&self) -> bool {
    self.opts.populate
  }
}

impl Options {
  /// Sets the option for read access.
  ///
  /// This option, when true, will indicate that the file should be
  /// `read`-able if opened.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_read(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_read(mut self, read: bool) -> Self {
    self.read = read;
    self
  }

  /// Sets the option for write access.
  ///
  /// This option, when true, will indicate that the file should be
  /// `write`-able if opened.
  ///
  /// If the file already exists, any write calls on it will overwrite its
  /// contents, without truncating it.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_write(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_write(mut self, write: bool) -> Self {
    self.write = write;
    self
  }

  /// Sets the option for the append mode.
  ///
  /// This option, when true, means that writes will append to a file instead
  /// of overwriting previous contents.
  /// Note that setting `.write(true).append(true)` has the same effect as
  /// setting only `.append(true)`.
  ///
  /// For most filesystems, the operating system guarantees that all writes are
  /// atomic: no writes get mangled because another process writes at the same
  /// time.
  ///
  /// One maybe obvious note when using append-mode: make sure that all data
  /// that belongs together is written to the file in one operation. This
  /// can be done by concatenating strings before passing them to [`write()`],
  /// or using a buffered writer (with a buffer of adequate size),
  /// and calling [`flush()`] when the message is complete.
  ///
  /// If a file is opened with both read and append access, beware that after
  /// opening, and after every write, the position for reading may be set at the
  /// end of the file. So, before writing, save the current position (using
  /// <code>[seek]\([SeekFrom](std::io::SeekFrom)::[Current]\(opts))</code>), and restore it before the next read.
  ///
  /// ## Note
  ///
  /// This function doesn't create the file if it doesn't exist. Use the
  /// [`Options::with_create`] method to do so.
  ///
  /// [`write()`]: std::io::Write::write "io::Write::write"
  /// [`flush()`]: std::io::Write::flush "io::Write::flush"
  /// [seek]: std::io::Seek::seek "io::Seek::seek"
  /// [Current]: std::io::SeekFrom::Current "io::SeekFrom::Current"
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_append(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_append(mut self, append: bool) -> Self {
    self.write = true;
    self.append = append;
    self
  }

  /// Sets the option for truncating a previous file.
  ///
  /// If a file is successfully opened with this option set it will truncate
  /// the file to opts length if it already exists.
  ///
  /// The file must be opened with write access for truncate to work.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_write(true).with_truncate(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_truncate(mut self, truncate: bool) -> Self {
    self.truncate = truncate;
    self.write = true;
    self
  }

  /// Sets the option to create a new file, or open it if it already exists.
  /// If the file does not exist, it is created and set the lenght of the file to the given size.
  ///
  /// In order for the file to be created, [`Options::with_write`] or
  /// [`Options::with_append`] access must be used.
  ///
  /// See also [`std::fs::write()`][std::fs::write] for a simple function to
  /// create a file with some given data.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_write(true).with_create(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_create(mut self, val: bool) -> Self {
    self.create = val;
    self
  }

  /// Sets the option to create a new file and set the file length to the given value, failing if it already exists.
  ///
  /// No file is allowed to exist at the target location, also no (dangling) symlink. In this
  /// way, if the call succeeds, the file returned is guaranteed to be new.
  ///
  /// This option is useful because it is atomic. Otherwise between checking
  /// whether a file exists and creating a new one, the file may have been
  /// created by another process (a TOCTOU race condition / attack).
  ///
  /// If `.with_create_new(true)` is set, [`.with_create()`](Options::with_create) and [`.with_truncate()`](Options::with_truncate) are
  /// ignored.
  ///
  /// The file must be opened with write or append access in order to create
  /// a new file.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let file = Options::new()
  ///   .with_write(true)
  ///   .with_create_new(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_create_new(mut self, val: bool) -> Self {
    self.create_new = val;
    self
  }

  /// Configures the memory map to start at byte `offset` from the beginning of the file.
  ///
  /// This option has no effect on anonymous memory maps or vec backed [`Allocator`](crate::Allocator).
  ///
  /// By default, the offset is 0.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_offset(30);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_offset(mut self, offset: u64) -> Self {
    self.offset = offset;
    self
  }

  /// Configures the anonymous memory map to be suitable for a process or thread stack.
  ///
  /// This option corresponds to the `MAP_STACK` flag on Linux. It has no effect on Windows.
  ///
  /// This option has no effect on file-backed memory maps and vec backed [`Allocator`](crate::Allocator).
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::Options;
  ///
  /// let stack = Options::new().with_stack(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_stack(mut self, stack: bool) -> Self {
    self.stack = stack;
    self
  }

  /// Configures the anonymous memory map to be allocated using huge pages.
  ///
  /// This option corresponds to the `MAP_HUGETLB` flag on Linux. It has no effect on Windows.
  ///
  /// The size of the requested page can be specified in page bits. If not provided, the system
  /// default is requested. The requested length should be a multiple of this, or the mapping
  /// will fail.
  ///
  /// This option has no effect on file-backed memory maps and vec backed [`Allocator`](crate::Allocator).
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::Options;
  ///
  /// let stack = Options::new().with_huge(Some(8));
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_huge(mut self, page_bits: Option<u8>) -> Self {
    self.huge = page_bits;
    self
  }

  /// Populate (prefault) page tables for a mapping.
  ///
  /// For a file mapping, this causes read-ahead on the file. This will help to reduce blocking on page faults later.
  ///
  /// This option corresponds to the `MAP_POPULATE` flag on Linux. It has no effect on Windows.
  ///
  /// This option has no effect on vec backed [`Allocator`](crate::Allocator).
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_populate(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_populate(mut self, populate: bool) -> Self {
    self.populate = populate;
    self
  }
}

impl Options {
  /// Returns `true` if the file should be opened with read access.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_read(true);
  /// assert_eq!(opts.read(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn read(&self) -> bool {
    self.read
  }

  /// Returns `true` if the file should be opened with write access.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_write(true);
  /// assert_eq!(opts.write(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn write(&self) -> bool {
    self.write
  }

  /// Returns `true` if the file should be opened with append access.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_append(true);
  /// assert_eq!(opts.append(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn append(&self) -> bool {
    self.append
  }

  /// Returns `true` if the file should be opened with truncate access.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_truncate(true);
  /// assert_eq!(opts.truncate(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn truncate(&self) -> bool {
    self.truncate
  }

  /// Returns `true` if the file should be created if it does not exist.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_create(true);
  /// assert_eq!(opts.create(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn create(&self) -> bool {
    self.create
  }

  /// Returns `true` if the file should be created if it does not exist and fail if it does.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_create_new(true);
  /// assert_eq!(opts.create_new(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn create_new(&self) -> bool {
    self.create_new
  }

  /// Returns the offset of the memory map.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_offset(30);
  /// assert_eq!(opts.offset(), 30);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn offset(&self) -> u64 {
    self.offset
  }

  /// Returns `true` if the memory map should be suitable for a process or thread stack.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_stack(true);
  /// assert_eq!(opts.stack(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn stack(&self) -> bool {
    self.stack
  }

  /// Returns the page bits of the memory map.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_huge(Some(8));
  /// assert_eq!(opts.huge(), Some(8));
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn huge(&self) -> Option<u8> {
    self.huge
  }

  /// Returns `true` if the memory map should populate (prefault) page tables for a mapping.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_populate(true);
  /// assert_eq!(opts.populate(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn populate(&self) -> bool {
    self.populate
  }
}
