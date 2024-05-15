use fs4::FileExt;
use memmap2::MmapOptions as Mmap2Options;
use std::{
  fs::{File, OpenOptions as StdOpenOptions},
  io,
  path::Path,
};

/// Options for opening a file for memory mapping.
pub struct OpenOptions {
  opts: StdOpenOptions,
  create: Option<u64>,
  create_new: Option<u64>,
  shrink_on_drop: bool,
  lock_shared: bool,
  lock_exclusive: bool,
}

impl From<StdOpenOptions> for OpenOptions {
  fn from(opts: StdOpenOptions) -> Self {
    Self {
      opts,
      create_new: None,
      create: None,
      shrink_on_drop: false,
      lock_shared: false,
      lock_exclusive: true,
    }
  }
}

impl Default for OpenOptions {
  /// Creates a blank new set of options ready for configuration.
  ///
  /// All options are initially set to `false`.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use skl::OpenOptions;
  ///
  /// let options = OpenOptions::default();
  /// ```
  fn default() -> Self {
    Self::new()
  }
}

impl OpenOptions {
  /// Creates a blank new set of options ready for configuration.
  ///
  /// All options are initially set to `false`.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use skl::OpenOptions;
  ///
  /// let mut options = OpenOptions::new();
  /// ```
  #[inline]
  pub fn new() -> Self {
    Self {
      opts: StdOpenOptions::new(),
      create: None,
      create_new: None,
      shrink_on_drop: false,
      lock_shared: false,
      lock_exclusive: true,
    }
  }

  /// Sets the option for read access.
  ///
  /// This option, when true, will indicate that the file should be
  /// `read`-able if opened.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use skl::OpenOptions;
  ///
  /// let opts = OpenOptions::new().read(true);
  /// ```
  #[inline]
  pub fn read(mut self, read: bool) -> Self {
    self.opts.read(read);
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
  /// # Examples
  ///
  /// ```rust
  /// use skl::OpenOptions;
  ///
  /// let opts = OpenOptions::new().write(true);
  /// ```
  #[inline]
  pub fn write(mut self, write: bool) -> Self {
    self.opts.write(write);
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
  /// [`OpenOptions::create`] method to do so.
  ///
  /// [`write()`]: std::io::Write::write "io::Write::write"
  /// [`flush()`]: std::io::Write::flush "io::Write::flush"
  /// [seek]: std::io::Seek::seek "io::Seek::seek"
  /// [Current]: std::io::SeekFrom::Current "io::SeekFrom::Current"
  ///
  /// # Examples
  ///
  /// ```rust
  /// use skl::OpenOptions;
  ///
  /// let opts = OpenOptions::new().append(true);
  /// ```
  #[inline]
  pub fn append(mut self, append: bool) -> Self {
    self.opts.append(append);
    self
  }

  /// Sets the option for truncating a previous file.
  ///
  /// If a file is successfully opened with this option set it will truncate
  /// the file to opts length if it already exists.
  ///
  /// The file must be opened with write access for truncate to work.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use skl::OpenOptions;
  ///
  /// let opts = OpenOptions::new().write(true).truncate(true);
  /// ```
  #[inline]
  pub fn truncate(mut self, truncate: bool) -> Self {
    self.opts.truncate(truncate);
    self
  }

  /// Sets the option to create a new file, or open it if it already exists.
  /// If the file does not exist, it is created and set the lenght of the file to the given size.
  ///
  /// In order for the file to be created, [`OpenOptions::write`] or
  /// [`OpenOptions::append`] access must be used.
  ///
  /// See also [`std::fs::write()`][std::fs::write] for a simple function to
  /// create a file with some given data.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use skl::OpenOptions;
  ///
  /// let opts = OpenOptions::new().write(true).create(Some(1000));
  /// ```
  ///
  /// ```rust
  /// use skl::OpenOptions;
  ///
  /// let opts = OpenOptions::new().write(true).create(None);
  /// ```
  #[inline]
  pub fn create(mut self, size: Option<u64>) -> Self {
    match size {
      Some(size) => {
        self.opts.create(true);
        self.create = Some(size);
      }
      None => {
        self.opts.create(false);
        self.create = None;
      }
    }
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
  /// If `.create_new(true)` is set, [`.create()`] and [`.truncate()`] are
  /// ignored.
  ///
  /// The file must be opened with write or append access in order to create
  /// a new file.
  ///
  /// [`.create()`]: OpenOptions::create
  /// [`.truncate()`]: OpenOptions::truncate
  ///
  /// # Examples
  ///
  /// ```rust
  /// use skl::OpenOptions;
  ///
  /// let file = OpenOptions::new()
  ///   .write(true)
  ///   .create_new(Some(1000));
  /// ```
  ///
  /// ```rust
  /// use skl::OpenOptions;
  ///
  /// let opts = OpenOptions::new()
  ///   .write(true)
  ///   .create_new(None);
  /// ```
  #[inline]
  pub fn create_new(mut self, size: Option<u64>) -> Self {
    match size {
      Some(size) => {
        self.opts.create_new(true);
        self.create_new = Some(size);
      }
      None => {
        self.opts.create_new(false);
        self.create_new = None;
      }
    }
    self
  }

  /// Sets the option to make the file shrink to the used size when dropped.
  ///
  /// This option, when true, will indicate that the file should be shrunk to
  /// the size of the data written to it when the file is dropped.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use skl::OpenOptions;
  ///
  /// let opts = OpenOptions::new().shrink_on_drop(true);
  /// ```
  #[inline]
  pub fn shrink_on_drop(mut self, shrink_on_drop: bool) -> Self {
    self.shrink_on_drop = shrink_on_drop;
    self
  }

  /// Sets the option to lock the file for shared read access.
  ///
  /// This option, when true, will indicate that the file should be locked for
  /// shared read access.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use skl::OpenOptions;
  ///
  /// let opts = OpenOptions::new().lock_shared(true);
  /// ```
  #[inline]
  pub fn lock_shared(mut self, lock_shared: bool) -> Self {
    self.lock_shared = lock_shared;
    self
  }

  /// Sets the option to lock the file for exclusive write access.
  ///
  /// This option, when true, will indicate that the file should be locked for
  /// exclusive write access.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use skl::OpenOptions;
  ///
  /// let opts = OpenOptions::new().lock_exclusive(true);
  /// ```
  #[inline]
  pub fn lock_exclusive(mut self, lock_exclusive: bool) -> Self {
    self.lock_exclusive = lock_exclusive;
    self
  }

  pub(crate) fn open<P: AsRef<Path>>(&self, path: P) -> io::Result<File> {
    if let Some(size) = self.create_new {
      return self.opts.open(path).and_then(|f| {
        if self.lock_exclusive {
          f.lock_exclusive()?;
        } else if self.lock_shared {
          f.lock_shared()?;
        }

        f.set_len(size).map(|_| f)
      });
    }

    if let Some(size) = self.create {
      return if path.as_ref().exists() {
        self.opts.open(path).and_then(|f| {
          if self.lock_exclusive {
            f.lock_exclusive()?;
          } else if self.lock_shared {
            f.lock_shared()?;
          }
          Ok(f)
        })
      } else {
        self.opts.open(path).and_then(|f| {
          if self.lock_exclusive {
            f.lock_exclusive()?;
          } else if self.lock_shared {
            f.lock_shared()?;
          }

          f.set_len(size).map(|_| f)
        })
      };
    }

    self.opts.open(path).and_then(|f| {
      if self.lock_exclusive {
        f.lock_exclusive()?;
      } else if self.lock_shared {
        f.lock_shared()?;
      }
      Ok(f)
    })
  }

  #[inline]
  pub(crate) const fn is_lock(&self) -> bool {
    self.lock_shared || self.lock_exclusive
  }

  #[inline]
  pub(crate) const fn is_shrink_on_drop(&self) -> bool {
    self.shrink_on_drop
  }
}

/// A memory map options for file backed [`SkipMap`](super::SkipMap) and [`SkipSet`](super::SkipSet),
/// providing advanced options and flags for specifying memory map behavior.
#[derive(Clone, Debug)]
pub struct MmapOptions(Mmap2Options);

impl Default for MmapOptions {
  fn default() -> Self {
    Self::new()
  }
}

impl From<Mmap2Options> for MmapOptions {
  fn from(opts: Mmap2Options) -> Self {
    Self(opts)
  }
}

impl MmapOptions {
  /// Creates a new set of options for configuring and creating a memory map.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::MmapOptions;
  ///
  /// // Create a new memory map options.
  /// let mut mmap_options = MmapOptions::new();
  /// ```
  #[inline]
  pub fn new() -> Self {
    Self(Mmap2Options::new())
  }

  /// Configures the created memory mapped buffer to be `len` bytes long.
  ///
  /// This option is mandatory for anonymous memory maps.
  ///
  /// For file-backed memory maps, the length will default to the file length.
  ///
  /// # Example
  ///
  /// ```
  /// use skl::MmapOptions;
  ///
  /// let opts = MmapOptions::new().len(9);
  /// ```
  #[inline]
  pub fn len(mut self, len: usize) -> Self {
    self.0.len(len);
    self
  }

  /// Configures the memory map to start at byte `offset` from the beginning of the file.
  ///
  /// This option has no effect on anonymous memory maps.
  ///
  /// By default, the offset is 0.
  ///
  /// # Example
  ///
  /// ```
  /// use skl::MmapOptions;
  ///
  /// let opts = MmapOptions::new().offset(30);
  /// ```
  #[inline]
  pub fn offset(mut self, offset: u64) -> Self {
    self.0.offset(offset);
    self
  }

  /// Configures the anonymous memory map to be suitable for a process or thread stack.
  ///
  /// This option corresponds to the `MAP_STACK` flag on Linux. It has no effect on Windows.
  ///
  /// This option has no effect on file-backed memory maps.
  ///
  /// # Example
  ///
  /// ```
  /// use skl::MmapOptions;
  ///
  /// let stack = MmapOptions::new().stack();
  /// ```
  #[inline]
  pub fn stack(mut self) -> Self {
    self.0.stack();
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
  /// This option has no effect on file-backed memory maps.
  ///
  /// # Example
  ///
  /// ```
  /// use skl::MmapOptions;
  ///
  /// let stack = MmapOptions::new().huge(Some(21)).len(2*1024*1024);
  /// ```
  #[inline]
  pub fn huge(mut self, page_bits: Option<u8>) -> Self {
    self.0.huge(page_bits);
    self
  }

  /// Populate (prefault) page tables for a mapping.
  ///
  /// For a file mapping, this causes read-ahead on the file. This will help to reduce blocking on page faults later.
  ///
  /// This option corresponds to the `MAP_POPULATE` flag on Linux. It has no effect on Windows.
  ///
  /// # Example
  ///
  /// ```
  /// use skl::MmapOptions;
  ///
  ///
  /// let opts = MmapOptions::new().populate();
  /// ```
  #[inline]
  pub fn populate(mut self) -> Self {
    self.0.populate();
    self
  }

  #[inline]
  pub(crate) unsafe fn map(&self, file: &File) -> io::Result<memmap2::Mmap> {
    self.0.map(file)
  }

  #[inline]
  pub(crate) unsafe fn map_mut(&self, file: &File) -> io::Result<memmap2::MmapMut> {
    self.0.map_mut(file)
  }

  #[inline]
  pub(crate) fn map_anon(&self) -> io::Result<memmap2::MmapMut> {
    self.0.map_anon()
  }
}
