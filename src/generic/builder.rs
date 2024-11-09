use core::mem;

use super::super::Options;
use crate::{
  allocator::Sealed,
  error::Error,
  options::{CompressionPolicy, Freelist},
  traits::Constructable,
  types::{Height, KeySize},
  Arena,
};

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
mod memmap;

/// A builder for creating a generic key-value `SkipMap`.
#[derive(Debug, Clone)]
pub struct Builder {
  options: Options,
}

impl Default for Builder {
  #[inline]
  fn default() -> Self {
    Self::new()
  }
}

impl From<Options> for Builder {
  #[inline]
  fn from(options: Options) -> Self {
    Self { options }
  }
}

impl From<Builder> for Options {
  #[inline]
  fn from(builder: Builder) -> Self {
    builder.options
  }
}

impl Builder {
  /// Create a new builder with the given options.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::generic::Builder;
  ///
  /// let builder = Builder::new();
  /// ```
  #[inline]
  pub const fn new() -> Self {
    Self {
      options: Options::new(),
    }
  }

  /// Get the options of the builder.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::generic::Builder;
  ///
  /// let builder = Builder::new();
  /// let options = builder.options();
  /// ```
  #[inline]
  pub const fn options(&self) -> &Options {
    &self.options
  }

  /// Set the options for the builder.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{generic::Builder, Options};
  ///
  /// let builder = Builder::new().with_options(Options::new());
  /// ```
  #[inline]
  pub const fn with_options(mut self, opts: Options) -> Self {
    self.options = opts;
    self
  }

  /// Returns the data offset of the `SkipMap` if the `SkipMap` is in unified memory layout.
  ///
  /// See also [`Builder::data_offset`].
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{generic::{unique::sync, multiple_version::unsync, Builder}, Arena};
  ///
  /// let opts = Builder::new().with_capacity(1024);
  /// let data_offset_from_opts = opts.data_offset::<sync::SkipMap<[u8], [u8]>>();
  /// let map = opts.alloc::<sync::SkipMap<[u8], [u8]>>().unwrap();
  /// assert_eq!(data_offset_from_opts, map.data_offset());
  ///
  /// let opts = Builder::new().with_capacity(1024);
  /// let data_offset_from_opts = opts.data_offset_unify::<sync::SkipMap<[u8], [u8]>>();
  /// let map = opts.with_unify(true).alloc::<sync::SkipMap<[u8], [u8]>>().unwrap();
  /// assert_eq!(data_offset_from_opts, map.data_offset());
  ///
  /// // Create a unsync ARENA.
  /// let opts = Builder::new().with_capacity(1024);
  /// let data_offset_from_opts = opts.data_offset::<unsync::SkipMap<[u8], [u8]>>();
  /// let map = opts.alloc::<unsync::SkipMap<[u8], [u8]>>().unwrap();
  /// assert_eq!(data_offset_from_opts, map.data_offset());
  ///
  /// let opts = Builder::new().with_capacity(1024);
  /// let data_offset_from_opts = opts.data_offset_unify::<unsync::SkipMap<[u8], [u8]>>();
  /// let map = opts.with_unify(true).alloc::<unsync::SkipMap<[u8], [u8]>>().unwrap();
  /// assert_eq!(data_offset_from_opts, map.data_offset());
  /// ```
  pub fn data_offset_unify<A>(&self) -> usize
  where
    A: Arena,
  {
    let arena_opts = self.options.to_arena_options();
    let arena_data_offset =
        arena_opts.data_offset_unify::<<<A::Constructable as Constructable>::Allocator as crate::allocator::Sealed>::Allocator>();

    crate::options::data_offset_in::<<A::Constructable as Constructable>::Allocator>(
      arena_data_offset,
      self.max_height(),
      true,
    )
  }

  /// Returns the data offset of the `SkipMap` if the `SkipMap` is not in unified memory layout.
  ///
  /// As the file backed `SkipMap` will only use the unified memory layout and ignore the unify configuration of `Options`,
  /// so see also [`Builder::data_offset_unify`], if you want to get the data offset of the `SkipMap` in unified memory layout.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{generic::{unique::sync, multiple_version::unsync, Builder}, Arena};
  ///
  /// let opts = Builder::new().with_capacity(1024);
  /// let data_offset_from_opts = opts.data_offset::<sync::SkipMap<[u8], [u8]>>();
  /// let map = opts.alloc::<sync::SkipMap<[u8], [u8]>>().unwrap();
  /// assert_eq!(data_offset_from_opts, map.data_offset());
  ///
  /// let opts = Builder::new().with_capacity(1024);
  /// let data_offset_from_opts = opts.data_offset_unify::<sync::SkipMap<[u8], [u8]>>();
  /// let map = opts.with_unify(true).alloc::<sync::SkipMap<[u8], [u8]>>().unwrap();
  /// assert_eq!(data_offset_from_opts, map.data_offset());
  ///
  /// // Create a unsync ARENA.
  /// let opts = Builder::new().with_capacity(1024);
  /// let data_offset_from_opts = opts.data_offset::<unsync::SkipMap<[u8], [u8]>>();
  /// let map = opts.alloc::<unsync::SkipMap<[u8], [u8]>>().unwrap();
  /// assert_eq!(data_offset_from_opts, map.data_offset());
  ///
  /// let opts = Builder::new().with_capacity(1024);
  /// let data_offset_from_opts = opts.data_offset_unify::<unsync::SkipMap<[u8], [u8]>>();
  /// let map = opts.with_unify(true).alloc::<unsync::SkipMap<[u8], [u8]>>().unwrap();
  /// assert_eq!(data_offset_from_opts, map.data_offset());
  /// ```
  pub fn data_offset<A>(&self) -> usize
  where
    A: Arena,
  {
    let arena_opts = self.options.to_arena_options();
    let arena_data_offset =
        arena_opts.data_offset::<<<A::Constructable as Constructable>::Allocator as crate::allocator::Sealed>::Allocator>();
    crate::options::data_offset_in::<<A::Constructable as Constructable>::Allocator>(
      arena_data_offset,
      self.max_height(),
      false,
    )
  }

  crate::__builder_opts!(generic::Builder);
}

impl Builder {
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
  /// use skl::generic::{unique::sync, multiple_version::unsync, Builder};
  ///
  /// let map = Builder::new().with_capacity(1024).alloc::<sync::SkipMap<[u8], [u8]>>().unwrap();
  ///
  /// let arena = Builder::new().with_capacity(1024).alloc::<unsync::SkipMap<[u8], [u8]>>().unwrap();
  /// ```
  #[inline]
  pub fn alloc<T>(self) -> Result<T, Error>
  where
    T: Arena,
    T::Constructable: Constructable<Comparator = ()>,
  {
    let node_align =
      mem::align_of::<<<T::Constructable as Constructable>::Allocator as Sealed>::Node>();

    let Builder { options } = self;
    options
      .to_arena_options()
      .with_maximum_alignment(node_align)
      .alloc::<<<T::Constructable as Constructable>::Allocator as Sealed>::Allocator>()
      .map_err(Into::into)
      .and_then(|arena| T::construct(arena, options, false, ()))
  }
}
