use core::mem;

use dbutils::{Ascend, Comparator};

use rarena_allocator::Options as ArenaOptions;

pub use rarena_allocator::Freelist;

use super::{allocator::Sealed, traits::Container, Error, Height, KeySize};

mod options;
pub use options::*;

/// The memory format version.
pub(crate) const CURRENT_VERSION: u16 = 0;

/// The builder to build `SkipMap`
pub struct Builder<C = Ascend> {
  pub(super) opts: Options,
  cmp: C,
}

impl Default for Builder {
  #[inline]
  fn default() -> Self {
    Self::new()
  }
}

impl Builder {
  /// Create a new `Builder` with default values.
  #[inline]
  pub const fn new() -> Self {
    Self {
      opts: Options::new(),
      cmp: Ascend,
    }
  }
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
    self.opts.reserved = reserved;
    self
  }

  /// Set if lock the meta of the ARENA in the memory to prevent OS from swapping out the first page of ARENA.
  /// When using memory map backed ARENA, the meta of the ARENA
  /// is in the first page, meta is frequently accessed,
  /// lock (`mlock` on the first page) the meta can reduce the page fault,
  /// but yes, this means that one `SkipMap` will have one page are locked in memory,
  /// and will not be swapped out. So, this is a trade-off between performance and memory usage.
  ///
  /// Default is `true`.
  ///
  /// This configuration has no effect on windows and vec backed ARENA.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::Builder;
  ///
  /// let opts = Builder::new().with_lock_meta(false);
  /// ```
  #[inline]
  pub const fn with_lock_meta(mut self, lock_meta: bool) -> Self {
    self.opts.lock_meta = lock_meta;
    self
  }

  /// Set the magic version of the [`Arena`](crate::traits::Arena).
  ///
  /// This is used by the application using [`Arena`](crate::traits::Arena)
  /// to ensure that it doesn't open the [`Arena`](crate::traits::Arena)
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

  /// Set the [`Freelist`] kind of the [`Arena`](crate::traits::Arena).
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

  /// Set the compression policy of the key in [`Arena`](crate::traits::Arena).
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
  #[cfg(feature = "experimental")]
  #[cfg_attr(docsrs, doc(cfg(feature = "experimental")))]
  #[inline]
  pub const fn with_compression_policy(mut self, policy: CompressionPolicy) -> Self {
    self.opts.policy = policy;
    self
  }

  /// Set if use the unify memory layout of the [`Arena`](crate::traits::Arena).
  ///
  /// File backed [`Arena`](crate::traits::Arena) has different memory layout with other kind backed [`Arena`](crate::traits::Arena),
  /// set this value to `true` will unify the memory layout of the [`Arena`](crate::traits::Arena), which means
  /// all kinds of backed [`Arena`](crate::traits::Arena) will have the same memory layout.
  ///
  /// This value will be ignored if the [`Arena`](crate::traits::Arena) is backed by a file backed memory map.
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
    self.opts.capacity = Some(capacity);
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

  /// Get if lock the meta of the ARENA in the memory to prevent OS from swapping out the first page of ARENA.
  /// When using memory map backed ARENA, the meta of the ARENA
  /// is in the first page, meta is frequently accessed,
  /// lock (`mlock` on the first page) the meta can reduce the page fault,
  /// but yes, this means that one `SkipMap` will have one page are locked in memory,
  /// and will not be swapped out. So, this is a trade-off between performance and memory usage.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::Builder;
  ///
  /// let opts = Builder::new().with_lock_meta(false);
  ///
  /// assert_eq!(opts.lock_meta(), false);
  /// ```
  #[inline]
  pub const fn lock_meta(&self) -> bool {
    self.opts.lock_meta
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
    self.opts.capacity()
  }

  /// Get if use the unify memory layout of the [`Arena`](crate::traits::Arena).
  ///
  /// File backed [`Arena`](crate::traits::Arena) has different memory layout with other kind backed [`Arena`](crate::traits::Arena),
  /// set this value to `true` will unify the memory layout of the [`Arena`](crate::traits::Arena), which means
  /// all kinds of backed [`Arena`](crate::traits::Arena) will have the same memory layout.
  ///
  /// This value will be ignored if the [`Arena`](crate::traits::Arena) is backed by a file backed memory map.
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

  /// Get the magic version of the [`Arena`](crate::traits::Arena).
  ///
  /// This is used by the application using [`Arena`](crate::traits::Arena)
  /// to ensure that it doesn't open the [`Arena`](crate::traits::Arena)
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

  /// Get the [`Freelist`] kind of the [`Arena`](crate::traits::Arena).
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

  /// Get the compression policy of the key in [`Arena`](crate::traits::Arena).
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
  #[cfg(feature = "experimental")]
  #[cfg_attr(docsrs, doc(cfg(feature = "experimental")))]
  #[inline]
  pub const fn compression_policy(&self) -> CompressionPolicy {
    self.opts.policy
  }
}

impl<C: Comparator> Builder<C> {
  /// Create a new map which is backed by a `AlignedVec`.
  ///
  /// **Note:** The capacity stands for how many memory allocated,
  /// it does not mean the skiplist can store `cap` entries.
  ///
  /// **What the difference between this method and [`Builder::map_anon`]?**
  ///
  /// 1. This method will use an `AlignedVec` ensures we are working within Rust's memory safety guarantees.
  ///    Even if we are working with raw pointers with `Box::into_raw`,
  ///    the backend ARENA will reclaim the ownership of this memory by converting it back to a `Box`
  ///    when dropping the backend ARENA. Since `AlignedVec` uses heap memory, the data might be more cache-friendly,
  ///    especially if you're frequently accessing or modifying it.
  ///
  /// 2. Where as [`Builder::map_anon`] will use mmap anonymous to require memory from the OS.
  ///    If you require very large contiguous memory regions, `mmap` might be more suitable because
  ///    it's more direct in requesting large chunks of memory from the OS.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{full::sync, trailed::unsync, Builder};
  ///
  /// // Create a sync skipmap which supports both trailer and version.
  /// let map = Builder::new().with_capacity(1024).alloc::<sync::SkipMap>().unwrap();
  ///
  /// // Create a unsync skipmap which supports trailer.
  /// let arena = Builder::new().with_capacity(1024).alloc::<unsync::SkipMap>().unwrap();
  /// ```
  #[inline]
  pub fn alloc<T: Container<Comparator = C>>(self) -> Result<T, Error> {
    let Self { opts, cmp } = self;

    let node_align = mem::align_of::<<T::Allocator as Sealed>::Node>();
    let trailer_align = mem::align_of::<<T::Allocator as Sealed>::Trailer>();

    opts
      .to_arena_options()
      .with_maximum_alignment(node_align.max(trailer_align))
      .alloc::<<T::Allocator as Sealed>::Allocator>()
      .map_err(Into::into)
      .and_then(|arena| T::construct(arena, opts, cmp, false))
  }
}
