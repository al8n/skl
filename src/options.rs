#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
pub use rarena_allocator::{MmapOptions, OpenOptions};

pub use rarena_allocator::Freelist;

use crate::{Height, KeySize};

/// Configuration for the compression policy of the key in [`SkipMap`](super::SkipMap).
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum CompressionPolicy {
  /// Fast compression policy, which only checks if the key is a prefix of the next key.
  #[default]
  Fast,
  /// High compression policy, which checks if the key is a substring of the next key.
  High,
}

/// Options for [`SkipMap`](super::SkipMap).
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
    }
  }

  /// Set the magic version of the [`SkipMap`](super::SkipMap).
  ///
  /// This is used by the application using [`SkipMap`](super::SkipMap)
  /// to ensure that it doesn't open the [`SkipMap`](super::SkipMap)
  /// with incompatible data format.
  ///  
  /// The default value is `0`.
  ///
  /// # Example
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

  /// Set the [`Freelist`] kind of the [`SkipMap`](super::SkipMap).
  ///
  /// The default value is [`Freelist::Optimistic`].
  ///
  /// # Example
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

  /// Set the compression policy of the key in [`SkipMap`](super::SkipMap).
  ///
  /// The default value is [`CompressionPolicy::Fast`].
  ///
  /// # Example
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

  /// Set if use the unify memory layout of the [`SkipMap`](super::SkipMap).
  ///
  /// File backed [`SkipMap`](super::SkipMap) has different memory layout with other kind backed [`SkipMap`](super::SkipMap),
  /// set this value to `true` will unify the memory layout of the [`SkipMap`](super::SkipMap), which means
  /// all kinds of backed [`SkipMap`](super::SkipMap) will have the same memory layout.
  ///
  /// This value will be ignored if the [`SkipMap`](super::SkipMap) is backed by a file backed memory map.
  ///
  /// The default value is `false`.
  ///
  /// # Example
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
  /// # Example
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
  /// # Example
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
  /// # Example
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
  /// # Example
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

  /// Returns the maximum size of the value.
  ///
  /// Default is `u32::MAX`. The maximum size of the value is `u32::MAX - header`.
  ///
  /// # Example
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
  /// # Example
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
  /// # Example
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
  /// # Example
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

  /// Get if use the unify memory layout of the [`SkipMap`](super::SkipMap).
  ///
  /// File backed [`SkipMap`](super::SkipMap) has different memory layout with other kind backed [`SkipMap`](super::SkipMap),
  /// set this value to `true` will unify the memory layout of the [`SkipMap`](super::SkipMap), which means
  /// all kinds of backed [`SkipMap`](super::SkipMap) will have the same memory layout.
  ///
  /// This value will be ignored if the [`SkipMap`](super::SkipMap) is backed by a file backed memory map.
  ///  
  /// The default value is `false`.
  ///
  /// # Example
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

  /// Get the magic version of the [`SkipMap`](super::SkipMap).
  ///
  /// This is used by the application using [`SkipMap`](super::SkipMap)
  /// to ensure that it doesn't open the [`SkipMap`](super::SkipMap)
  /// with incompatible data format.
  ///
  /// The default value is `0`.
  ///
  /// # Example
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

  /// Get the [`Freelist`] kind of the [`SkipMap`](super::SkipMap).
  ///
  /// The default value is [`Freelist::Optimistic`].
  ///
  /// # Example
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

  /// Get the compression policy of the key in [`SkipMap`](super::SkipMap).
  ///
  /// The default value is [`CompressionPolicy::Fast`].
  ///
  /// # Example
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
