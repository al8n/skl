mod list;

/// Dynamic key-value `SkipMap` implementation with multiple versions support.
pub mod multiple_version;

/// Dynamic key-value `SkipMap` implementation without multiple versions support.
pub mod unique;

mod builder;
pub use builder::Builder;

/// Iterators for the skipmaps.
pub mod iter {
  pub use super::list::iterator::Iter;
}

/// Entry references for the skipmaps.
pub mod entry {
  pub use super::list::EntryRef;
}

pub use dbutils::equivalentor::*;

/// The value of an entry in the [`SkipMap`].
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct Value<T: ?Sized>(T);

impl<T> core::fmt::Debug for Value<T>
where
  T: core::fmt::Debug + ?Sized,
{
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.0.fmt(f)
  }
}

/// Value that can be converted from a byte slice.
pub trait FromValueBytes<'a>: sealed::Sealed<'a> {}

impl<'a, T> FromValueBytes<'a> for T where T: sealed::Sealed<'a> {}

mod sealed {
  pub trait Sealed<'a> {
    type Ref;

    fn as_ref(&self) -> Self::Ref;

    fn from_value_bytes(src: Option<&'a [u8]>) -> Self
    where
      Self: 'a;

    fn is_removed(&self) -> bool;
  }

  impl<'a> Sealed<'a> for Option<&'a [u8]> {
    type Ref = Option<&'a [u8]>;

    #[inline]
    fn as_ref(&self) -> Self::Ref {
      self.as_ref().copied()
    }

    #[inline]
    fn from_value_bytes(src: Option<&'a [u8]>) -> Self {
      src
    }

    #[inline]
    fn is_removed(&self) -> bool {
      self.is_none()
    }
  }

  impl<'a> Sealed<'a> for &'a [u8] {
    type Ref = Self;

    #[inline]
    fn as_ref(&self) -> Self::Ref {
      self
    }

    #[inline]
    fn from_value_bytes(src: Option<&'a [u8]>) -> Self {
      match src {
        Some(v) => v,
        None => panic!("cannot convert None to Value"),
      }
    }

    #[inline]
    fn is_removed(&self) -> bool {
      false
    }
  }
}
