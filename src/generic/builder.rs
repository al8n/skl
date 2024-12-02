use core::mem;

use super::{super::Options, Ascend};
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
#[derive(Debug)]
pub struct Builder<C = Ascend<[u8]>> {
  options: Options,
  cmp: C,
}

impl<C> Default for Builder<C>
where
  C: Default,
{
  #[inline]
  fn default() -> Self {
    Self {
      options: Options::default(),
      cmp: Default::default(),
    }
  }
}

impl<C: Default> From<Options> for Builder<C> {
  #[inline]
  fn from(options: Options) -> Self {
    Self {
      options,
      cmp: Default::default(),
    }
  }
}

impl<C> From<Builder<C>> for Options {
  #[inline]
  fn from(builder: Builder<C>) -> Self {
    builder.options
  }
}

impl<C> Builder<C> {
  /// Create a new builder with the given options.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::generic::{Builder, Ascend};
  ///
  /// let builder = Builder::with(Ascend::<[u8]>::new());
  /// ```
  #[inline]
  pub const fn with(cmp: C) -> Self {
    Self {
      options: Options::new(),
      cmp,
    }
  }
}

impl<C: Default> Builder<C> {
  /// Create a new builder with the given options.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::generic::{Builder, Ascend};
  ///
  /// let builder = Builder::<Ascend<str>>::new();
  /// ```
  #[inline]
  pub fn new() -> Self {
    Self {
      options: Options::new(),
      cmp: Default::default(),
    }
  }
}

impl<C> Builder<C> {
  /// Get the comparator of the builder.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::generic::{Builder, Ascend};
  ///
  /// let builder = Builder::<Ascend<str>>::new().comparator();
  /// ```
  #[inline]
  pub const fn comparator(&self) -> &C {
    &self.cmp
  }

  /// Set the comparator for the builder.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::generic::{Builder, Ascend};
  ///
  /// let builder = Builder::<Ascend<[u8]>>::new().with_comparator(Ascend::<Vec<u8>>::new());
  ///
  /// assert_eq!(builder.comparator(), &Ascend::new());
  /// ```
  #[inline]
  pub fn with_comparator<NC>(self, cmp: NC) -> Builder<NC> {
    Builder {
      options: self.options,
      cmp,
    }
  }

  /// Get the options of the builder.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::generic::{Builder, Ascend};
  ///
  /// let builder = Builder::<Ascend<str>>::new();
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
  /// let builder: Builder = Builder::new().with_options(Options::new());
  /// ```
  #[inline]
  pub const fn with_options(mut self, opts: Options) -> Self {
    self.options = opts;
    self
  }

  crate::__builder_opts!(generic::Builder);
}

impl<C> Builder<C> {
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
  /// use skl::generic::{unique::sync, multiple_version::unsync, Builder, Ascend};
  ///
  /// let map = Builder::<Ascend<[u8]>>::new().with_capacity(1024).alloc::<sync::SkipMap<[u8], [u8]>>().unwrap();
  ///
  /// let arena = Builder::<Ascend<[u8]>>::new().with_capacity(1024).alloc::<unsync::SkipMap<[u8], [u8]>>().unwrap();
  /// ```
  #[inline]
  pub fn alloc<T>(self) -> Result<T, Error>
  where
    T: Arena,
    T::Constructable: Constructable<Comparator = C>,
  {
    let node_align =
      mem::align_of::<<<T::Constructable as Constructable>::Allocator as Sealed>::Node>();

    let Builder { options, cmp, .. } = self;
    options
      .to_arena_options()
      .with_maximum_alignment(node_align)
      .alloc::<<<T::Constructable as Constructable>::Allocator as Sealed>::Allocator>()
      .map_err(Into::into)
      .and_then(|arena| T::construct(arena, options, false, cmp))
  }
}
