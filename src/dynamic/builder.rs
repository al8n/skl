use core::mem;

use dbutils::equivalentor::{Ascend, DynComparator};

use crate::{
  allocator::Sealed,
  error::Error,
  options::{CompressionPolicy, Freelist},
  traits::Constructable,
  types::{Height, KeySize},
  Arena, Options,
};

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
mod memmap;

/// A builder for creating a dynamic key-value `SkipMap`.
#[derive(Debug, Clone)]
pub struct Builder<C = Ascend> {
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
      options: Options::new(),
      cmp: C::default(),
    }
  }
}

impl<C> From<Options> for Builder<C>
where
  C: Default,
{
  #[inline]
  fn from(options: Options) -> Self {
    Self {
      options,
      cmp: C::default(),
    }
  }
}

impl<C> From<Builder<C>> for Options {
  #[inline]
  fn from(builder: Builder<C>) -> Self {
    builder.options
  }
}

impl Builder {
  /// Create a new builder with the given options.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::dynamic::Builder;
  ///
  /// let builder = Builder::new();
  /// ```
  #[inline]
  pub const fn new() -> Self {
    Self {
      options: Options::new(),
      cmp: Ascend,
    }
  }
}

impl<C> Builder<C> {
  /// Get the options of the builder.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::dynamic::Builder;
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
  /// use skl::{dynamic::Builder, Options};
  ///
  /// let builder = Builder::new().with_options(Options::default());
  /// ```
  #[inline]
  pub fn with_options(self, options: Options) -> Self {
    Self {
      options,
      cmp: self.cmp,
    }
  }

  /// Get the comparator of the builder.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::dynamic::Builder;
  ///
  /// let builder = Builder::new().comparator();
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
  /// use skl::dynamic::{Builder, Descend};
  ///
  /// let builder = Builder::new().with_comparator(Descend);
  ///
  /// assert_eq!(builder.comparator(), &Descend);
  /// ```
  #[inline]
  pub fn with_comparator<NC>(self, cmp: NC) -> Builder<NC> {
    Builder {
      options: self.options,
      cmp,
    }
  }

  crate::__builder_opts!(dynamic::Builder);
}

impl<C: DynComparator<[u8], [u8]>> Builder<C> {
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
  /// use skl::dynamic::{unique::sync, multiple_version::unsync, Builder};
  ///
  /// let map = Builder::new().with_capacity(1024).alloc::<sync::SkipMap>().unwrap();
  ///
  /// let arena = Builder::new().with_capacity(1024).alloc::<unsync::SkipMap>().unwrap();
  /// ```
  #[inline]
  pub fn alloc<T>(self) -> Result<T, Error>
  where
    T: Arena,
    T::Constructable: Constructable<Comparator = C>,
  {
    let node_align =
      mem::align_of::<<<T::Constructable as Constructable>::Allocator as Sealed>::Node>();

    let Self { options, cmp } = self;
    options
      .to_arena_options()
      .with_maximum_alignment(node_align)
      .alloc::<<<T::Constructable as Constructable>::Allocator as Sealed>::Allocator>()
      .map_err(Into::into)
      .and_then(|arena| T::construct(arena, options, false, cmp))
  }
}
