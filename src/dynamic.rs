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

pub use dbutils::equivalentor::{BytesComparator, BytesRangeComparator};

/// Ascend is a comparator that compares byte slices in ascending order.
pub type Ascend = dbutils::equivalentor::Ascend<[u8]>;

/// Ascend is a comparator that compares byte slices in ascending order.
pub type Descend = dbutils::equivalentor::Descend<[u8]>;

/// Value that can be converted from a byte slice.
pub trait Value<'a>: sealed::Sealed<'a> {}

impl<'a, T> Value<'a> for T where T: sealed::Sealed<'a> {}

mod sealed {
  pub trait Sealed<'a> {
    type Ref;

    fn as_ref(&self) -> Self::Ref;

    fn from_value_bytes(src: Option<&'a [u8]>) -> Self
    where
      Self: 'a;

    fn is_removed(&self) -> bool;

    fn all_versions(&self) -> bool;
  }

  impl<'a> Sealed<'a> for Option<&'a [u8]> {
    type Ref = Self;

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

    #[inline]
    fn all_versions(&self) -> bool {
      true
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

    #[inline]
    fn all_versions(&self) -> bool {
      false
    }
  }
}
