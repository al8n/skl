mod builder;
mod list;

/// Generic `SkipMap` implementation with multiple versions support.
pub mod multiple_version;

/// Generic `SkipMap` implementation without multiple versions support.
pub mod unique;

/// Iterators for the skipmaps.
pub mod iter {
  pub use super::list::iterator::Iter;
}

/// Entry references for the skipmaps.
pub mod entry {
  pub use super::list::EntryRef;
}

pub use builder::Builder;

pub use dbutils::{equivalent::*, types::*};

/// Value that can be converted from a byte slice.
pub trait GenericValue<'a>: sealed::Sealed<'a> {}

impl<'a, T> GenericValue<'a> for T where T: sealed::Sealed<'a> {}

mod sealed {
  use dbutils::types::{LazyRef, Type};

  pub trait Sealed<'a> {
    type Ref;
    type Value: Type + ?Sized;

    fn as_ref(&self) -> Self::Ref;

    fn from_bytes(src: Option<&'a [u8]>) -> Self
    where
      Self: 'a;

    fn from_lazy_ref(src: Option<LazyRef<'a, Self::Value>>) -> Self
    where
      Self: 'a;

    fn raw(&self) -> Option<&'a [u8]>;

    fn is_removed(&self) -> bool;

    fn all_versions(&self) -> bool;
  }

  impl<'a, T> Sealed<'a> for Option<LazyRef<'a, T>>
  where
    T: Type + ?Sized,
  {
    type Ref = Option<T::Ref<'a>>;
    type Value = T;

    #[inline]
    fn as_ref(&self) -> Self::Ref {
      self.as_ref().map(|v| *v.get())
    }

    #[inline]
    fn from_bytes(src: Option<&'a [u8]>) -> Self {
      src.map(|v| unsafe { LazyRef::from_raw(v) })
    }

    #[inline]
    fn from_lazy_ref(src: Option<LazyRef<'a, Self::Value>>) -> Self {
      src
    }

    #[inline]
    fn raw(&self) -> Option<&'a [u8]> {
      self
        .as_ref()
        .map(|v| v.raw().expect("raw value must be available"))
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

  impl<'a, T> Sealed<'a> for LazyRef<'a, T>
  where
    T: Type + ?Sized,
  {
    type Ref = T::Ref<'a>;
    type Value = T;

    #[inline]
    fn as_ref(&self) -> Self::Ref {
      *self.get()
    }

    #[inline]
    fn from_bytes(src: Option<&'a [u8]>) -> Self {
      match src {
        Some(v) => unsafe { LazyRef::from_raw(v) },
        None => panic!("cannot convert None to Value"),
      }
    }

    #[inline]
    fn from_lazy_ref(src: Option<LazyRef<'a, Self::Value>>) -> Self {
      match src {
        Some(v) => v,
        None => panic!("cannot convert None to Value"),
      }
    }

    #[inline]
    fn raw(&self) -> Option<&'a [u8]> {
      LazyRef::raw(self)
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
