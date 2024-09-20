use core::mem;

use dbutils::{Ascend, Comparator};

use rarena_allocator::{Allocator as _, ArenaOptions};
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
pub use rarena_allocator::{MmapOptions, OpenOptions};

pub use rarena_allocator::Freelist;

use crate::{allocator::AllocatorExt, error::invalid_data};

use super::{
  allocator::{Allocator, Sealed},
  Constructable, Error, Height, KeySize, CURRENT_VERSION,
};

/// Configuration for the compression policy of the key in [`Map`](super::Map).
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum CompressionPolicy {
  /// Fast compression policy, which only checks if the key is a prefix of the next key.
  #[default]
  Fast,
  /// High compression policy, which checks if the key is a substring of the next key.
  High,
}

/// Options for [`Map`](super::Map).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Options {
  max_value_size: u32,
  max_key_size: KeySize,
  max_height: Height,
  magic_version: u16,
  capacity: u32,
  unify: bool,
  freelist: Freelist,
  policy: CompressionPolicy,
  reserved: u32,
}

impl Default for Options {
  #[inline]
  fn default() -> Options {
    Options::new()
  }
}

impl Options {
  /// Creates a new set of options with the default values.
  #[inline]
  pub const fn new() -> Self {
    Self {
      max_value_size: u32::MAX,
      max_key_size: KeySize::MAX,
      max_height: Height::new(),
      capacity: 1024,
      unify: false,
      magic_version: 0,
      freelist: Freelist::Optimistic,
      policy: CompressionPolicy::Fast,
      reserved: 0,
    }
  }

  /// Set the reserved bytes of the ARENA.
  ///
  /// The reserved is used to configure the start position of the ARENA. This is useful
  /// when you want to add some bytes before the ARENA, e.g. when using the memory map file backed ARENA,
  /// you can set the reserved to the size to `8` to store a 8 bytes checksum.
  ///
  /// The default reserved is `0`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_reserved(8);
  /// ```
  #[inline]
  pub const fn with_reserved(mut self, reserved: u32) -> Self {
    self.reserved = if self.capacity <= reserved {
      self.capacity
    } else {
      reserved
    };
    self
  }

  /// Set the magic version of the [`Map`](super::Map).
  ///
  /// This is used by the application using [`Map`](super::Map)
  /// to ensure that it doesn't open the [`Map`](super::Map)
  /// with incompatible data format.
  ///  
  /// The default value is `0`.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_magic_version(1);
  /// ```
  #[inline]
  pub const fn with_magic_version(mut self, magic_version: u16) -> Self {
    self.magic_version = magic_version;
    self
  }

  /// Set the [`Freelist`] kind of the [`Map`](super::Map).
  ///
  /// The default value is [`Freelist::Optimistic`].
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::{Options, options::Freelist};
  ///
  /// let opts = Options::new().with_freelist(Freelist::Optimistic);
  /// ```
  #[inline]
  pub const fn with_freelist(mut self, freelist: Freelist) -> Self {
    self.freelist = freelist;
    self
  }

  /// Set the compression policy of the key in [`Map`](super::Map).
  ///
  /// The default value is [`CompressionPolicy::Fast`].
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::{Options, options::CompressionPolicy};
  ///
  /// let opts = Options::new().with_compression_policy(CompressionPolicy::High);
  /// ```
  #[inline]
  pub const fn with_compression_policy(mut self, policy: CompressionPolicy) -> Self {
    self.policy = policy;
    self
  }

  /// Set if use the unify memory layout of the [`Map`](super::Map).
  ///
  /// File backed [`Map`](super::Map) has different memory layout with other kind backed [`Map`](super::Map),
  /// set this value to `true` will unify the memory layout of the [`Map`](super::Map), which means
  /// all kinds of backed [`Map`](super::Map) will have the same memory layout.
  ///
  /// This value will be ignored if the [`Map`](super::Map) is backed by a file backed memory map.
  ///
  /// The default value is `false`.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_unify(true);
  /// ```
  #[inline]
  pub const fn with_unify(mut self, unify: bool) -> Self {
    self.unify = unify;
    self
  }

  /// Sets the maximum size of the value.
  ///
  /// Default is `u32::MAX`.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::Options;
  ///
  /// let options = Options::new().with_max_value_size(1024);
  /// ```
  #[inline]
  pub const fn with_max_value_size(mut self, size: u32) -> Self {
    self.max_value_size = size;
    self
  }

  /// Sets the maximum size of the key.
  ///
  /// The maximum size of the key is `u27::MAX`.
  ///
  /// Default is `65535`.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::{Options, KeySize};
  ///
  /// let options = Options::new().with_max_key_size(KeySize::new());
  /// ```
  #[inline]
  pub const fn with_max_key_size(mut self, size: KeySize) -> Self {
    self.max_key_size = size;
    self
  }

  /// Sets the maximum height.
  ///
  /// Default is `20`. The maximum height is `31`. The minimum height is `1`.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::{Options, Height};
  ///
  /// let options = Options::new().with_max_height(Height::new());
  /// ```
  #[inline]
  pub const fn with_max_height(mut self, height: Height) -> Self {
    self.max_height = height;
    self
  }

  /// Sets the capacity of the underlying ARENA.
  ///
  /// Default is `1024`. This configuration will be ignored if the map is memory-mapped.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::Options;
  ///
  /// let options = Options::new().with_capacity(1024);
  /// ```
  #[inline]
  pub const fn with_capacity(mut self, capacity: u32) -> Self {
    self.capacity = capacity;
    self
  }

  /// Get the reserved of the ARENA.
  ///
  /// The reserved is used to configure the start position of the ARENA. This is useful
  /// when you want to add some bytes before the ARENA, e.g. when using the memory map file backed ARENA,
  /// you can set the reserved to the size to `8` to store a 8 bytes checksum.
  ///
  /// The default reserved is `0`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_reserved(8);
  ///
  /// assert_eq!(opts.reserved(), 8);
  /// ```
  #[inline]
  pub const fn reserved(&self) -> u32 {
    self.reserved
  }

  /// Returns the maximum size of the value.
  ///
  /// Default is `u32::MAX`. The maximum size of the value is `u32::MAX - header`.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::Options;
  ///
  /// let options = Options::new().with_max_value_size(1024);
  /// ```
  #[inline]
  pub const fn max_value_size(&self) -> u32 {
    self.max_value_size
  }

  /// Returns the maximum size of the key.
  ///
  /// The maximum size of the key is `u27::MAX`.
  ///
  /// Default is `65535`.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::{Options, KeySize};
  ///
  /// let options = Options::new().with_max_key_size(KeySize::new());
  ///
  /// assert_eq!(options.max_key_size(), u16::MAX);
  /// ```
  #[inline]
  pub const fn max_key_size(&self) -> KeySize {
    self.max_key_size
  }

  /// Returns the maximum height.
  ///
  /// Default is `20`. The maximum height is `31`. The minimum height is `1`.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::{Options, Height};
  ///
  /// let options = Options::new().with_max_height(Height::from_u8_unchecked(5));
  ///
  /// assert_eq!(options.max_height(), 5);
  /// ```
  #[inline]
  pub const fn max_height(&self) -> Height {
    self.max_height
  }

  /// Returns the configuration of underlying ARENA size.
  ///
  /// Default is `1024`. This configuration will be ignored if the map is memory-mapped.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let options = Options::new().with_capacity(1024);
  /// ```
  #[inline]
  pub const fn capacity(&self) -> u32 {
    self.capacity
  }

  /// Get if use the unify memory layout of the [`Map`](super::Map).
  ///
  /// File backed [`Map`](super::Map) has different memory layout with other kind backed [`Map`](super::Map),
  /// set this value to `true` will unify the memory layout of the [`Map`](super::Map), which means
  /// all kinds of backed [`Map`](super::Map) will have the same memory layout.
  ///
  /// This value will be ignored if the [`Map`](super::Map) is backed by a file backed memory map.
  ///  
  /// The default value is `false`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_unify(true);
  ///
  /// assert_eq!(opts.unify(), true);
  /// ```
  #[inline]
  pub const fn unify(&self) -> bool {
    self.unify
  }

  /// Get the magic version of the [`Map`](super::Map).
  ///
  /// This is used by the application using [`Map`](super::Map)
  /// to ensure that it doesn't open the [`Map`](super::Map)
  /// with incompatible data format.
  ///
  /// The default value is `0`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_magic_version(1);
  ///
  /// assert_eq!(opts.magic_version(), 1);
  /// ```
  #[inline]
  pub const fn magic_version(&self) -> u16 {
    self.magic_version
  }

  /// Get the [`Freelist`] kind of the [`Map`](super::Map).
  ///
  /// The default value is [`Freelist::Optimistic`].
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{Options, options::Freelist};
  ///
  /// let opts = Options::new().with_freelist(Freelist::Optimistic);
  ///
  /// assert_eq!(opts.freelist(), Freelist::Optimistic);
  /// ```
  #[inline]
  pub const fn freelist(&self) -> Freelist {
    self.freelist
  }

  /// Get the compression policy of the key in [`Map`](super::Map).
  ///
  /// The default value is [`CompressionPolicy::Fast`].
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{Options, options::CompressionPolicy};
  ///
  /// let opts = Options::new().with_compression_policy(CompressionPolicy::High);
  ///
  /// assert_eq!(opts.compression_policy(), CompressionPolicy::High);
  /// ```
  #[inline]
  pub const fn compression_policy(&self) -> CompressionPolicy {
    self.policy
  }
}

/// The builder to build a `Map`
pub struct Builder<C = Ascend> {
  opts: Options,
  cmp: C,
}

impl<C> Builder<C> {
  /// Returns a new map builder with the new [`Comparator`](super::Comparator).
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{Builder, Descend};
  ///
  /// let builder = Builder::new().with_comparator(Descend);
  /// ```
  #[inline]
  pub fn with_comparator<NC>(self, cmp: NC) -> Builder<NC> {
    Builder {
      cmp,
      opts: self.opts,
    }
  }

  /// Returns a new map builder with the new [`Options`].
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{Builder, Options};
  ///
  /// let builder = Builder::new().with_options(Options::new().with_capacity(1024));
  /// ```
  #[inline]
  pub const fn with_options(mut self, opts: Options) -> Self {
    self.opts = opts;
    self
  }

  /// Set the reserved bytes of the ARENA.
  ///
  /// The reserved is used to configure the start position of the ARENA. This is useful
  /// when you want to add some bytes before the ARENA, e.g. when using the memory map file backed ARENA,
  /// you can set the reserved to the size to `8` to store a 8 bytes checksum.
  ///
  /// The default reserved is `0`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::Builder;
  ///
  /// let builder = Builder::new().with_reserved(8);
  /// ```
  #[inline]
  pub const fn with_reserved(mut self, reserved: u32) -> Self {
    self.opts.reserved = if self.opts.capacity <= reserved {
      self.opts.capacity
    } else {
      reserved
    };
    self
  }

  /// Set the magic version of the [`Map`](super::Map).
  ///
  /// This is used by the application using [`Map`](super::Map)
  /// to ensure that it doesn't open the [`Map`](super::Map)
  /// with incompatible data format.
  ///  
  /// The default value is `0`.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::Builder;
  ///
  /// let builder = Builder::new().with_magic_version(1);
  /// ```
  #[inline]
  pub const fn with_magic_version(mut self, magic_version: u16) -> Self {
    self.opts.magic_version = magic_version;
    self
  }

  /// Set the [`Freelist`] kind of the [`Map`](super::Map).
  ///
  /// The default value is [`Freelist::Optimistic`].
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::{Builder, Freelist};
  ///
  /// let builder = Builder::new().with_freelist(Freelist::Optimistic);
  /// ```
  #[inline]
  pub const fn with_freelist(mut self, freelist: Freelist) -> Self {
    self.opts.freelist = freelist;
    self
  }

  /// Set the compression policy of the key in [`Map`](super::Map).
  ///
  /// The default value is [`CompressionPolicy::Fast`].
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::{Builder, CompressionPolicy};
  ///
  /// let builder = Builder::new().with_compression_policy(CompressionPolicy::High);
  /// ```
  #[inline]
  pub const fn with_compression_policy(mut self, policy: CompressionPolicy) -> Self {
    self.opts.policy = policy;
    self
  }

  /// Set if use the unify memory layout of the [`Map`](super::Map).
  ///
  /// File backed [`Map`](super::Map) has different memory layout with other kind backed [`Map`](super::Map),
  /// set this value to `true` will unify the memory layout of the [`Map`](super::Map), which means
  /// all kinds of backed [`Map`](super::Map) will have the same memory layout.
  ///
  /// This value will be ignored if the [`Map`](super::Map) is backed by a file backed memory map.
  ///
  /// The default value is `false`.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::Builder;
  ///
  /// let builder = Builder::new().with_unify(true);
  /// ```
  #[inline]
  pub const fn with_unify(mut self, unify: bool) -> Self {
    self.opts.unify = unify;
    self
  }

  /// Sets the maximum size of the value.
  ///
  /// Default is `u32::MAX`.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::Builder;
  ///
  /// let builder = Builder::new().with_max_value_size(1024);
  /// ```
  #[inline]
  pub const fn with_max_value_size(mut self, size: u32) -> Self {
    self.opts.max_value_size = size;
    self
  }

  /// Sets the maximum size of the key.
  ///
  /// The maximum size of the key is `u27::MAX`.
  ///
  /// Default is `65535`.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::{Builder, KeySize};
  ///
  /// let builder = Builder::new().with_max_key_size(KeySize::new());
  /// ```
  #[inline]
  pub const fn with_max_key_size(mut self, size: KeySize) -> Self {
    self.opts.max_key_size = size;
    self
  }

  /// Sets the maximum height.
  ///
  /// Default is `20`. The maximum height is `31`. The minimum height is `1`.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::{Builder, Height};
  ///
  /// let builder = Builder::new().with_max_height(Height::new());
  /// ```
  #[inline]
  pub const fn with_max_height(mut self, height: Height) -> Self {
    self.opts.max_height = height;
    self
  }

  /// Sets the capacity of the underlying ARENA.
  ///
  /// Default is `1024`. This configuration will be ignored if the map is memory-mapped.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::Builder;
  ///
  /// let builder = Builder::new().with_capacity(1024);
  /// ```
  #[inline]
  pub const fn with_capacity(mut self, capacity: u32) -> Self {
    self.opts.capacity = capacity;
    self
  }

  /// Get the reserved of the ARENA.
  ///
  /// The reserved is used to configure the start position of the ARENA. This is useful
  /// when you want to add some bytes before the ARENA, e.g. when using the memory map file backed ARENA,
  /// you can set the reserved to the size to `8` to store a 8 bytes checksum.
  ///
  /// The default reserved is `0`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::Builder;
  ///
  /// let builder = Builder::new().with_reserved(8);
  ///
  /// assert_eq!(builder.reserved(), 8);
  /// ```
  #[inline]
  pub const fn reserved(&self) -> u32 {
    self.opts.reserved
  }

  /// Returns the maximum size of the value.
  ///
  /// Default is `u32::MAX`. The maximum size of the value is `u32::MAX - header`.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::Builder;
  ///
  /// let builder = Builder::new().with_max_value_size(1024);
  /// ```
  #[inline]
  pub const fn max_value_size(&self) -> u32 {
    self.opts.max_value_size
  }

  /// Returns the maximum size of the key.
  ///
  /// The maximum size of the key is `u27::MAX`.
  ///
  /// Default is `65535`.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::{Builder, KeySize};
  ///
  /// let builder = Builder::new().with_max_key_size(KeySize::new());
  ///
  /// assert_eq!(builder.max_key_size(), u16::MAX);
  /// ```
  #[inline]
  pub const fn max_key_size(&self) -> KeySize {
    self.opts.max_key_size
  }

  /// Returns the maximum height.
  ///
  /// Default is `20`. The maximum height is `31`. The minimum height is `1`.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::{Builder, Height};
  ///
  /// let builder = Builder::new().with_max_height(Height::from_u8_unchecked(5));
  ///
  /// assert_eq!(builder.max_height(), 5);
  /// ```
  #[inline]
  pub const fn max_height(&self) -> Height {
    self.opts.max_height
  }

  /// Returns the configuration of underlying ARENA size.
  ///
  /// Default is `1024`. This configuration will be ignored if the map is memory-mapped.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::Builder;
  ///
  /// let builder = Builder::new().with_capacity(1024);
  /// ```
  #[inline]
  pub const fn capacity(&self) -> u32 {
    self.opts.capacity
  }

  /// Get if use the unify memory layout of the [`Map`](super::Map).
  ///
  /// File backed [`Map`](super::Map) has different memory layout with other kind backed [`Map`](super::Map),
  /// set this value to `true` will unify the memory layout of the [`Map`](super::Map), which means
  /// all kinds of backed [`Map`](super::Map) will have the same memory layout.
  ///
  /// This value will be ignored if the [`Map`](super::Map) is backed by a file backed memory map.
  ///  
  /// The default value is `false`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::Builder;
  ///
  /// let builder = Builder::new().with_unify(true);
  ///
  /// assert_eq!(builder.unify(), true);
  /// ```
  #[inline]
  pub const fn unify(&self) -> bool {
    self.opts.unify
  }

  /// Get the magic version of the [`Map`](super::Map).
  ///
  /// This is used by the application using [`Map`](super::Map)
  /// to ensure that it doesn't open the [`Map`](super::Map)
  /// with incompatible data format.
  ///
  /// The default value is `0`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::Builder;
  ///
  /// let builder = Builder::new().with_magic_version(1);
  ///
  /// assert_eq!(builder.magic_version(), 1);
  /// ```
  #[inline]
  pub const fn magic_version(&self) -> u16 {
    self.opts.magic_version
  }

  /// Get the [`Freelist`] kind of the [`Map`](super::Map).
  ///
  /// The default value is [`Freelist::Optimistic`].
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{Builder, Freelist};
  ///
  /// let builder = Builder::new().with_freelist(Freelist::Optimistic);
  ///
  /// assert_eq!(builder.freelist(), Freelist::Optimistic);
  /// ```
  #[inline]
  pub const fn freelist(&self) -> Freelist {
    self.opts.freelist
  }

  /// Get the compression policy of the key in [`Map`](super::Map).
  ///
  /// The default value is [`CompressionPolicy::Fast`].
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{Builder, CompressionPolicy};
  ///
  /// let builder = Builder::new().with_compression_policy(CompressionPolicy::High);
  ///
  /// assert_eq!(builder.compression_policy(), CompressionPolicy::High);
  /// ```
  #[inline]
  pub const fn compression_policy(&self) -> CompressionPolicy {
    self.opts.policy
  }
}

impl<C: Comparator> Builder<C> {
  /// Create a new [`Map`](super::Map) which is backed by a `Vec`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{sync, unsync};
  ///
  /// // Create a sync skipmap which supports both trailer and version.
  /// let map = Builder::new().alloc::<sync::full::SkipMap>().unwrap();
  ///
  /// // Create a unsync skipmap which supports trailer.
  /// let arena = Builder::new().alloc::<unsync::trailed::SkipMap>().unwrap();
  /// ```
  #[inline]
  pub fn alloc<T: Constructable<Comparator = C>>(self) -> Result<T, Error> {
    let Self { opts, cmp } = self;

    let node_align = mem::align_of::<<T::Allocator as Sealed>::Node>();
    let trailer_align = mem::align_of::<<T::Allocator as Sealed>::Trailer>();

    ArenaOptions::new()
      .with_capacity(opts.capacity())
      .with_maximum_alignment(node_align.max(trailer_align))
      .with_unify(opts.unify())
      .with_magic_version(CURRENT_VERSION)
      .with_freelist(opts.freelist())
      .with_reserved(opts.reserved())
      .alloc::<<T::Allocator as Sealed>::Allocator>()
      .map_err(Into::into)
      .and_then(|arena| T::new_in(arena, opts, cmp))
  }

  /// Create a new [`Map`](super::Map) which is backed by a anonymous memory map.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{sync, unsync, MmapOptions};
  ///
  /// // Create a sync skipmap which supports both trailer and version.
  /// let map = Builder::new().map_anon::<sync::full::SkipMap>(MmapOptions::new().len(1024)).unwrap();
  ///
  /// // Create a unsync skipmap which supports trailer.
  /// let arena = Builder::new().map_anon::<unsync::trailed::SkipMap>(MmapOptions::new().len(1024)).unwrap();
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub fn map_anon<T: Constructable<Comparator = C>>(self, mmap_options: MmapOptions) -> std::io::Result<T> {
    let Self { opts, cmp } = self;

    let node_align = mem::align_of::<<T::Allocator as Sealed>::Node>();
    let trailer_align = mem::align_of::<<T::Allocator as Sealed>::Trailer>();

    #[allow(clippy::bind_instead_of_map)]
    ArenaOptions::new()
      .with_capacity(opts.capacity())
      .with_maximum_alignment(node_align.max(trailer_align))
      .with_unify(opts.unify())
      .with_magic_version(CURRENT_VERSION)
      .with_freelist(opts.freelist())
      .with_reserved(opts.reserved())
      .map_anon::<<T::Allocator as Sealed>::Allocator>(mmap_options)
      .map_err(Into::into)
      .and_then(|arena| T::new_in(arena, opts, cmp)
        .map_err(invalid_data)
        .and_then(|map| {
          // Lock the memory of first page to prevent it from being swapped out.
          #[cfg(not(windows))]
          unsafe {
            let arena = map.allocator();
            arena
              .mlock(0, arena.page_size().min(arena.capacity()))?;
          }
          Ok(map)
        }))
  }

  /// Like [`SkipList::map`], but with a custom [`Comparator`].
  ///
  /// ## Safety
  /// - If trying to reopens a skiplist, then the trailer type must be the same as the previous one.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub unsafe fn map<P: AsRef<std::path::Path>>(
    self,
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    cmp: C,
  ) -> std::io::Result<Self> {
    let Self { opts, cmp } = self;

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
  /// ## Safety
  /// - If trying to reopens a skiplist, then the trailer type must be the same as the previous one.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub unsafe fn map_with_path_builder<PB, E>(
    self,
    path_builder: PB,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> Result<Self, Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    let Self { opts, cmp } = self;
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
}
