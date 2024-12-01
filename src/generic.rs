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

pub use dbutils::{
  equivalent::{Comparable, Equivalent},
  equivalentor::{
    Comparator, Equivalentor, TypeRefComparator, TypeRefEquivalentor, TypeRefQueryComparator,
    TypeRefQueryEquivalentor,
  },
  types::*,
};

/// The default stateless comparator.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DefaultComparator<K: ?Sized>(core::marker::PhantomData<K>);

impl<K: ?Sized> Clone for DefaultComparator<K> {
  #[inline]
  fn clone(&self) -> Self {
    *self
  }
}

impl<K: ?Sized> Copy for DefaultComparator<K> {}

impl<K: ?Sized> Default for DefaultComparator<K> {
  #[inline]
  fn default() -> Self {
    Self::new()
  }
}

impl<K: ?Sized> DefaultComparator<K> {
  /// Create a new default comparator.
  #[inline]
  pub const fn new() -> Self {
    Self(core::marker::PhantomData)
  }
}

impl<K: ?Sized> core::fmt::Debug for DefaultComparator<K> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("DefaultComparator").finish()
  }
}

impl<K> Equivalentor for DefaultComparator<K>
where
  K: Type + Ord + ?Sized,
{
  type Type = K;

  #[inline]
  fn equivalent(&self, a: &Self::Type, b: &Self::Type) -> bool {
    a == b
  }
}

impl<K> Comparator for DefaultComparator<K>
where
  K: Type + Ord + ?Sized,
{
  #[inline]
  fn compare(&self, a: &Self::Type, b: &Self::Type) -> core::cmp::Ordering {
    a.cmp(b)
  }
}

impl<'a, K> TypeRefEquivalentor<'a> for DefaultComparator<K>
where
  K: Type + Ord + ?Sized,
  K::Ref<'a>: KeyRef<'a, K> + Comparable<K>,
{
  #[inline]
  fn equivalent_ref(&self, a: &Self::Type, b: &<Self::Type as Type>::Ref<'a>) -> bool {
    Equivalent::equivalent(b, a)
  }

  #[inline]
  fn equivalent_refs(
    &self,
    a: &<Self::Type as Type>::Ref<'a>,
    b: &<Self::Type as Type>::Ref<'a>,
  ) -> bool {
    a == b
  }
}

impl<'a, K> TypeRefComparator<'a> for DefaultComparator<K>
where
  K: Type + Ord + ?Sized,
  K::Ref<'a>: KeyRef<'a, K> + Comparable<K>,
{
  #[inline]
  fn compare_ref(&self, a: &Self::Type, b: &<Self::Type as Type>::Ref<'a>) -> core::cmp::Ordering {
    Comparable::compare(b, a).reverse()
  }

  #[inline]
  fn compare_refs(
    &self,
    a: &<Self::Type as Type>::Ref<'a>,
    b: &<Self::Type as Type>::Ref<'a>,
  ) -> core::cmp::Ordering {
    a.cmp(b)
  }
}

impl<'a, K, Q> TypeRefQueryEquivalentor<'a, Q> for DefaultComparator<K>
where
  K: Type + Ord + ?Sized,
  K::Ref<'a>: KeyRef<'a, K> + Comparable<K>,
  Q: ?Sized + Comparable<K::Ref<'a>>,
{
  fn query_equivalent_ref(&self, a: &<Self::Type as Type>::Ref<'a>, b: &Q) -> bool {
    Equivalent::equivalent(b, a)
  }
}

impl<'a, K, Q> TypeRefQueryComparator<'a, Q> for DefaultComparator<K>
where
  K: Type + Ord + ?Sized,
  K::Ref<'a>: KeyRef<'a, K> + Comparable<K>,
  Q: ?Sized + Comparable<K::Ref<'a>>,
{
  #[inline]
  fn query_compare_ref(&self, a: &<Self::Type as Type>::Ref<'a>, b: &Q) -> core::cmp::Ordering {
    Comparable::compare(b, a).reverse()
  }
}

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
