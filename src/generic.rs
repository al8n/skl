use core::{marker::PhantomData, ops::{Bound, RangeBounds}};

use dbutils::{traits::{KeyRef, Type, TypeRef}, CheapClone, Comparator};

mod container;

struct GenericComparator<K: ?Sized> {
  _k: PhantomData<K>,
}

impl<K: ?Sized> CheapClone for GenericComparator<K> {}

impl<K: ?Sized> Clone for GenericComparator<K> {
  fn clone(&self) -> Self {
    *self
  }
}

impl<K: ?Sized> Copy for GenericComparator<K> {}

impl<K: ?Sized> core::fmt::Debug for GenericComparator<K> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("GenericComparator").finish()
  }
}

impl<K> Comparator for GenericComparator<K>
where
  K: ?Sized + Type,
  for<'a> K::Ref<'a>: KeyRef<'a, K>,
{
  fn compare(&self, a: &[u8], b: &[u8]) -> core::cmp::Ordering {
    unsafe { <K::Ref<'_> as KeyRef<'_, K>>::compare_binary(a, b) }
  }

  fn contains(&self, start_bound: Bound<&[u8]>, end_bound: Bound<&[u8]>, key: &[u8]) -> bool {
    unsafe {
      let start = start_bound.map(|b| <K::Ref<'_> as TypeRef<'_>>::from_slice(b));
      let end = end_bound.map(|b| <K::Ref<'_> as TypeRef<'_>>::from_slice(b));
      let key = <K::Ref<'_> as TypeRef<'_>>::from_slice(key);

      (start, end).contains(&key)
    }
  }
}

