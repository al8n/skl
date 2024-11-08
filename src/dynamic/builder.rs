use dbutils::equivalentor::Ascend;

use crate::{
  options::{CompressionPolicy, Freelist},
  types::{Height, KeySize},
  Options,
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
  /// use skl::dynamic::Builder;
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
