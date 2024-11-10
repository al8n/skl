use core::mem;

pub use rarena_allocator::Freelist;
use rarena_allocator::Options as ArenaOptions;

use crate::{
  allocator::{Node, Sealed as AllocatorSealed},
  types::{Height, KeySize},
};

/// The memory format version.
pub(crate) const CURRENT_VERSION: u16 = 0;

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
mod open_options;

/// Configuration for the compression policy of the key in [`Arena`](crate::traits::Arena).
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum CompressionPolicy {
  /// Fast compression policy, which only checks if the key is a prefix of the next key.
  #[default]
  Fast,
  /// High compression policy, which checks if the key is a substring of the next key.
  #[cfg(feature = "experimental")]
  #[cfg_attr(docsrs, doc(cfg(feature = "experimental")))]
  High,
}

/// Options for [`Arena`](crate::traits::Arena).
#[viewit::viewit(vis_all = "pub(super)", getters(skip), setters(skip))]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Options {
  max_value_size: u32,
  max_key_size: KeySize,
  max_height: Height,
  magic_version: u16,
  capacity: Option<u32>,
  unify: bool,
  freelist: Freelist,
  policy: CompressionPolicy,
  reserved: u32,
  lock_meta: bool,

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  create_new: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  create: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  read: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  write: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  append: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  truncate: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  offset: u64,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  stack: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  huge: Option<u8>,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  populate: bool,
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
      capacity: None,
      unify: false,
      magic_version: 0,
      freelist: Freelist::None,
      policy: CompressionPolicy::Fast,
      reserved: 0,
      lock_meta: true,

      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      create_new: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      create: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      read: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      write: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      append: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      truncate: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      offset: 0,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      stack: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      huge: None,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      populate: false,
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
    self.reserved = reserved;
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
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_lock_meta(false);
  /// ```
  #[inline]
  pub const fn with_lock_meta(mut self, lock_meta: bool) -> Self {
    self.lock_meta = lock_meta;
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
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_magic_version(1);
  /// ```
  #[inline]
  pub const fn with_magic_version(mut self, magic_version: u16) -> Self {
    self.magic_version = magic_version;
    self
  }

  /// Set the [`Freelist`] kind of the [`Arena`](crate::traits::Arena).
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

  /// Set the compression policy of the key in [`Arena`](crate::traits::Arena).
  ///
  /// The default value is [`CompressionPolicy::Fast`].
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::{Options, options::CompressionPolicy};
  ///
  /// let opts = Options::new().with_compression_policy(CompressionPolicy::Fast);
  /// ```
  #[inline]
  pub const fn with_compression_policy(mut self, policy: CompressionPolicy) -> Self {
    self.policy = policy;
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
  /// ## Example
  ///
  /// ```
  /// use skl::Options;
  ///
  /// let options = Options::new().with_capacity(1024);
  /// ```
  #[inline]
  pub const fn with_capacity(mut self, capacity: u32) -> Self {
    self.capacity = Some(capacity);
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
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_lock_meta(false);
  ///
  /// assert_eq!(opts.lock_meta(), false);
  /// ```
  #[inline]
  pub const fn lock_meta(&self) -> bool {
    self.lock_meta
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
  /// ## Example
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let options = Options::new().with_capacity(1024);
  /// ```
  #[inline]
  pub const fn capacity(&self) -> u32 {
    match self.capacity {
      Some(capacity) => capacity,
      None => 0,
    }
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

  /// Get the [`Freelist`] kind of the [`Arena`](crate::traits::Arena).
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

  /// Get the compression policy of the keys in [`Arena`](crate::traits::Arena).
  ///
  /// The default value is [`CompressionPolicy::Fast`].
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{Options, options::CompressionPolicy};
  ///
  /// let opts = Options::new().with_compression_policy(CompressionPolicy::Fast);
  ///
  /// assert_eq!(opts.compression_policy(), CompressionPolicy::Fast);
  /// ```
  #[inline]
  pub const fn compression_policy(&self) -> CompressionPolicy {
    self.policy
  }
}

impl Options {
  #[allow(clippy::wrong_self_convention)]
  #[inline]
  pub(super) const fn to_arena_options(&self) -> ArenaOptions {
    let opts = ArenaOptions::new()
      .with_magic_version(CURRENT_VERSION)
      .with_reserved(self.reserved())
      .with_unify(self.unify())
      .maybe_capacity(self.capacity)
      .with_freelist(self.freelist());

    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    {
      opts
        .with_lock_meta(false) // we need to avoid arena's lock_meta
        .with_create(self.create())
        .with_create_new(self.create_new())
        .with_read(self.read())
        .with_write(self.write())
        .with_append(self.append())
        .with_truncate(self.truncate())
        .with_offset(self.offset())
        .with_stack(self.stack())
        .with_huge(self.huge())
        .with_populate(self.populate())
    }

    #[cfg(not(all(feature = "memmap", not(target_family = "wasm"))))]
    opts
  }
}

#[inline]
pub(crate) fn data_offset_in<A: AllocatorSealed>(
  offset: usize,
  max_height: Height,
  unify: bool,
) -> usize {
  let meta_end = if unify {
    let alignment = mem::align_of::<A::Meta>();
    let meta_offset = (offset + alignment - 1) & !(alignment - 1);
    meta_offset + mem::size_of::<A::Meta>()
  } else {
    offset
  };

  let alignment = mem::align_of::<A::Node>();
  let head_offset = (meta_end + alignment - 1) & !(alignment - 1);
  let head_end = head_offset
    + mem::size_of::<A::Node>()
    + mem::size_of::<<A::Node as Node>::Link>() * max_height.to_usize();

  let tail_offset = (head_end + alignment - 1) & !(alignment - 1);
  tail_offset
    + mem::size_of::<A::Node>()
    + mem::size_of::<<A::Node as Node>::Link>() * max_height.to_usize()
}

#[macro_export]
#[doc(hidden)]
macro_rules! __builder_opts {
  ($mod:ident::$name:ident) => {
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
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_reserved(8);")]
    /// ```
    #[inline]
    pub const fn with_reserved(mut self, reserved: u32) -> Self {
      self.options.reserved = reserved;
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
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_lock_meta(false);")]
    /// ```
    #[inline]
    pub const fn with_lock_meta(mut self, lock_meta: bool) -> Self {
      self.options.lock_meta = lock_meta;
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
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_magic_version(1);")]
    /// ```
    #[inline]
    pub const fn with_magic_version(mut self, magic_version: u16) -> Self {
      self.options.magic_version = magic_version;
      self
    }

    /// Set the [`Freelist`] kind of the [`Arena`](crate::traits::Arena).
    ///
    /// The default value is [`Freelist::Optimistic`].
    ///
    /// ## Example
    ///
    /// ```
    #[doc = concat!("use skl::{", stringify!($mod), "::", stringify!($name), ", options::Freelist};")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_freelist(Freelist::Optimistic);")]
    /// ```
    #[inline]
    pub const fn with_freelist(mut self, freelist: Freelist) -> Self {
      self.options.freelist = freelist;
      self
    }

    /// Set the compression policy of the key in [`Arena`](crate::traits::Arena).
    ///
    /// The default value is [`CompressionPolicy::Fast`].
    ///
    /// ## Example
    ///
    /// ```
    #[doc = concat!("use skl::{", stringify!($mod), "::", stringify!($name), ", options::CompressionPolicy};")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_compression_policy(CompressionPolicy::Fast);")]
    /// ```
    #[inline]
    pub const fn with_compression_policy(mut self, policy: CompressionPolicy) -> Self {
      self.options.policy = policy;
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
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_unify(true);")]
    /// ```
    #[inline]
    pub const fn with_unify(mut self, unify: bool) -> Self {
      self.options.unify = unify;
      self
    }

    /// Sets the maximum size of the value.
    ///
    /// Default is `u32::MAX`.
    ///
    /// ## Example
    ///
    /// ```
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let options = ", stringify!($name), "::new().with_max_value_size(1024);")]
    /// ```
    #[inline]
    pub const fn with_max_value_size(mut self, size: u32) -> Self {
      self.options.max_value_size = size;
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
    #[doc = concat!("use skl::{", stringify!($mod), "::", stringify!($name), ", KeySize};")]
    ///
    #[doc = concat!("let options = ", stringify!($name), "::new().with_max_key_size(KeySize::new());")]
    /// ```
    #[inline]
    pub const fn with_max_key_size(mut self, size: KeySize) -> Self {
      self.options.max_key_size = size;
      self
    }

    /// Sets the maximum height.
    ///
    /// Default is `20`. The maximum height is `31`. The minimum height is `1`.
    ///
    /// ## Example
    ///
    /// ```rust
    #[doc = concat!("use skl::{", stringify!($mod), "::", stringify!($name), ", Height};")]
    ///
    #[doc = concat!("let options = ", stringify!($name), "::new().with_max_height(Height::new());")]
    /// ```
    #[inline]
    pub const fn with_max_height(mut self, height: Height) -> Self {
      self.options.max_height = height;
      self
    }

    /// Sets the capacity of the underlying ARENA.
    ///
    /// ## Example
    ///
    /// ```
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let options = ", stringify!($name), "::new().with_capacity(1024);")]
    /// ```
    #[inline]
    pub const fn with_capacity(mut self, capacity: u32) -> Self {
      self.options.capacity = Some(capacity);
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
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_reserved(8);")]
    ///
    /// assert_eq!(opts.reserved(), 8);
    /// ```
    #[inline]
    pub const fn reserved(&self) -> u32 {
      self.options.reserved
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
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_lock_meta(false);")]
    ///
    /// assert_eq!(opts.lock_meta(), false);
    /// ```
    #[inline]
    pub const fn lock_meta(&self) -> bool {
      self.options.lock_meta
    }

    /// Returns the maximum size of the value.
    ///
    /// Default is `u32::MAX`. The maximum size of the value is `u32::MAX - header`.
    ///
    /// ## Example
    ///
    /// ```
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let options = ", stringify!($name), "::new().with_max_value_size(1024);")]
    /// ```
    #[inline]
    pub const fn max_value_size(&self) -> u32 {
      self.options.max_value_size
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
    #[doc = concat!("use skl::{", stringify!($mod), "::", stringify!($name), ", KeySize};")]
    ///
    #[doc = concat!("let options = ", stringify!($name), "::new().with_max_key_size(KeySize::new());")]
    ///
    /// assert_eq!(options.max_key_size(), u16::MAX);
    /// ```
    #[inline]
    pub const fn max_key_size(&self) -> KeySize {
      self.options.max_key_size
    }

    /// Returns the maximum height.
    ///
    /// Default is `20`. The maximum height is `31`. The minimum height is `1`.
    ///
    /// ## Example
    ///
    /// ```
    #[doc = concat!("use skl::{", stringify!($mod), "::", stringify!($name), ", Height};")]
    ///
    #[doc = concat!("let options = ", stringify!($name), "::new().with_max_height(Height::from_u8_unchecked(5));")]
    ///
    /// assert_eq!(options.max_height(), 5);
    /// ```
    #[inline]
    pub const fn max_height(&self) -> Height {
      self.options.max_height
    }

    /// Returns the configuration of underlying ARENA size.
    ///
    /// ## Example
    ///
    /// ```rust
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let options = ", stringify!($name), "::new().with_capacity(1024);")]
    /// ```
    #[inline]
    pub const fn capacity(&self) -> u32 {
      match self.options.capacity {
        Some(capacity) => capacity,
        None => 0,
      }
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
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_unify(true);")]
    ///
    /// assert_eq!(opts.unify(), true);
    /// ```
    #[inline]
    pub const fn unify(&self) -> bool {
      self.options.unify
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
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_magic_version(1);")]
    ///
    /// assert_eq!(opts.magic_version(), 1);
    /// ```
    #[inline]
    pub const fn magic_version(&self) -> u16 {
      self.options.magic_version
    }

    /// Get the [`Freelist`] kind of the [`Arena`](crate::traits::Arena).
    ///
    /// The default value is [`Freelist::Optimistic`].
    ///
    /// ## Example
    ///
    /// ```rust
    #[doc = concat!("use skl::{", stringify!($mod), "::", stringify!($name), ", options::Freelist};")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_freelist(Freelist::Optimistic);")]
    ///
    /// assert_eq!(opts.freelist(), Freelist::Optimistic);
    /// ```
    #[inline]
    pub const fn freelist(&self) -> Freelist {
      self.options.freelist
    }

    /// Get the compression policy of the keys in [`Arena`](crate::traits::Arena).
    ///
    /// The default value is [`CompressionPolicy::Fast`].
    ///
    /// ## Example
    ///
    /// ```rust
    #[doc = concat!("use skl::{", stringify!($mod), "::", stringify!($name), ", options::CompressionPolicy};")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_compression_policy(CompressionPolicy::Fast);")]
    ///
    /// assert_eq!(opts.compression_policy(), CompressionPolicy::Fast);
    /// ```
    #[inline]
    pub const fn compression_policy(&self) -> CompressionPolicy {
      self.options.policy
    }

    /// Sets the option for read access.
    ///
    /// This option, when true, will indicate that the file should be
    /// `read`-able if opened.
    ///
    /// ## Examples
    ///
    /// ```rust
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_read(true);")]
    /// ```
    #[inline]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
    pub fn with_read(mut self, read: bool) -> Self {
      self.options.read = read;
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
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_write(true);")]
    /// ```
    #[inline]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
    pub fn with_write(mut self, write: bool) -> Self {
      self.options.write = write;
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
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_append(true);")]
    /// ```
    #[inline]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
    pub fn with_append(mut self, append: bool) -> Self {
      self.options.write = true;
      self.options.append = append;
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
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_write(true).with_truncate(true);")]
    /// ```
    #[inline]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
    pub fn with_truncate(mut self, truncate: bool) -> Self {
      self.options.truncate = truncate;
      self.options.write = true;
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
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_write(true).with_create(true);")]
    /// ```
    #[inline]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
    pub fn with_create(mut self, val: bool) -> Self {
      self.options.create = val;
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
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_write(true).with_create_new(true);")]
    /// ```
    #[inline]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
    pub fn with_create_new(mut self, val: bool) -> Self {
      self.options.create_new = val;
      self
    }

    /// Configures the memory map to start at byte `offset` from the beginning of the file.
    ///
    /// This option has no effect on anonymous memory maps or vec backed [`Arena`](crate::traits::Arena).
    ///
    /// By default, the offset is 0.
    ///
    /// ## Example
    ///
    /// ```
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_offset(30);")]
    /// ```
    #[inline]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
    pub fn with_offset(mut self, offset: u64) -> Self {
      self.options.offset = offset;
      self
    }

    /// Configures the anonymous memory map to be suitable for a process or thread stack.
    ///
    /// This option corresponds to the `MAP_STACK` flag on Linux. It has no effect on Windows.
    ///
    /// This option has no effect on file-backed memory maps and vec backed [`Arena`](crate::traits::Arena).
    ///
    /// ## Example
    ///
    /// ```
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let stack = ", stringify!($name), "::new().with_stack(true);")]
    /// ```
    #[inline]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
    pub fn with_stack(mut self, stack: bool) -> Self {
      self.options.stack = stack;
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
    /// This option has no effect on file-backed memory maps and vec backed [`Arena`](crate::traits::Arena).
    ///
    /// ## Example
    ///
    /// ```
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let huge = ", stringify!($name), "::new().with_huge(Some(8));")]
    /// ```
    #[inline]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
    pub fn with_huge(mut self, page_bits: Option<u8>) -> Self {
      self.options.huge = page_bits;
      self
    }

    /// Populate (prefault) page tables for a mapping.
    ///
    /// For a file mapping, this causes read-ahead on the file. This will help to reduce blocking on page faults later.
    ///
    /// This option corresponds to the `MAP_POPULATE` flag on Linux. It has no effect on Windows.
    ///
    /// This option has no effect on vec backed [`Arena`](crate::traits::Arena).
    ///
    /// ## Example
    ///
    /// ```
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let populate = ", stringify!($name), "::new().with_populate(true);")]
    /// ```
    #[inline]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
    pub fn with_populate(mut self, populate: bool) -> Self {
      self.options.populate = populate;
      self
    }

    /// Returns `true` if the file should be opened with read access.
    ///
    /// ## Examples
    ///
    /// ```rust
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_read(true);")]
    /// assert_eq!(opts.read(), true);
    /// ```
    #[inline]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
    pub const fn read(&self) -> bool {
      self.options.read
    }

    /// Returns `true` if the file should be opened with write access.
    ///
    /// ## Examples
    ///
    /// ```rust
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_write(true);")]
    /// assert_eq!(opts.write(), true);
    /// ```
    #[inline]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
    pub const fn write(&self) -> bool {
      self.options.write
    }

    /// Returns `true` if the file should be opened with append access.
    ///
    /// ## Examples
    ///
    /// ```rust
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_append(true);")]
    /// assert_eq!(opts.append(), true);
    /// ```
    #[inline]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
    pub const fn append(&self) -> bool {
      self.options.append
    }

    /// Returns `true` if the file should be opened with truncate access.
    ///
    /// ## Examples
    ///
    /// ```rust
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_truncate(true);")]
    /// assert_eq!(opts.truncate(), true);
    /// ```
    #[inline]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
    pub const fn truncate(&self) -> bool {
      self.options.truncate
    }

    /// Returns `true` if the file should be created if it does not exist.
    ///
    /// ## Examples
    ///
    /// ```rust
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_create(true);")]
    /// assert_eq!(opts.create(), true);
    /// ```
    #[inline]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
    pub const fn create(&self) -> bool {
      self.options.create
    }

    /// Returns `true` if the file should be created if it does not exist and fail if it does.
    ///
    /// ## Examples
    ///
    /// ```rust
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_create_new(true);")]
    /// assert_eq!(opts.create_new(), true);
    /// ```
    #[inline]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
    pub const fn create_new(&self) -> bool {
      self.options.create_new
    }

    /// Returns the offset of the memory map.
    ///
    /// ## Examples
    ///
    /// ```rust
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_offset(30);")]
    /// assert_eq!(opts.offset(), 30);
    /// ```
    #[inline]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
    pub const fn offset(&self) -> u64 {
      self.options.offset
    }

    /// Returns `true` if the memory map should be suitable for a process or thread stack.
    ///
    /// ## Examples
    ///
    /// ```rust
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_stack(true);")]
    /// assert_eq!(opts.stack(), true);
    /// ```
    #[inline]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
    pub const fn stack(&self) -> bool {
      self.options.stack
    }

    /// Returns the page bits of the memory map.
    ///
    /// ## Examples
    ///
    /// ```rust
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_huge(Some(8));")]
    /// assert_eq!(opts.huge(), Some(8));
    /// ```
    #[inline]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
    pub const fn huge(&self) -> Option<u8> {
      self.options.huge
    }

    /// Returns `true` if the memory map should populate (prefault) page tables for a mapping.
    ///
    /// ## Examples
    ///
    /// ```rust
    #[doc = concat!("use skl::", stringify!($mod), "::", stringify!($name), ";")]
    ///
    #[doc = concat!("let opts = ", stringify!($name), "::new().with_populate(true);")]
    /// assert_eq!(opts.populate(), true);
    /// ```
    #[inline]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
    pub const fn populate(&self) -> bool {
      self.options.populate
    }
  };
}
