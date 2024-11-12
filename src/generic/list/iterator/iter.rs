use core::ops::{Bound, RangeBounds};

use dbutils::{
  equivalent::Comparable,
  types::{KeyRef, Type},
};

use super::{
  super::{Allocator, EntryRef, RefCounter, SkipList, Version},
  IterAll,
};

/// An iterator over the skipmap. The current state of the iterator can be cloned by
/// simply value copying the struct.
pub struct Iter<'a, K, V, A, RC, Q = <K as Type>::Ref<'a>, R = core::ops::RangeFull>(
  IterAll<'a, K, V, A, RC, Q, R>,
)
where
  A: Allocator,
  RC: RefCounter,
  K: ?Sized + Type,
  V: ?Sized + Type,
  Q: ?Sized;

impl<K, V, A, RC, R: Clone, Q> Clone for Iter<'_, K, V, A, RC, Q, R>
where
  A: Allocator,
  RC: RefCounter,
  K: ?Sized + Type,
  V: ?Sized + Type,
  Q: ?Sized,
{
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<'a, K, V, A, RC> Iter<'a, K, V, A, RC>
where
  K: ?Sized + Type,
  K::Ref<'a>: KeyRef<'a, K>,
  V: ?Sized + Type,
  A: Allocator,
  RC: RefCounter,
{
  #[inline]
  pub(crate) const fn new(version: Version, map: &'a SkipList<K, V, A, RC>) -> Self {
    Self(IterAll::new(version, map, false))
  }
}

impl<'a, K, V, A, RC, Q, R> Iter<'a, K, V, A, RC, Q, R>
where
  K: ?Sized + Type,
  K::Ref<'a>: KeyRef<'a, K>,
  V: ?Sized + Type,
  A: Allocator,
  RC: RefCounter,
  Q: ?Sized,
{
  #[inline]
  pub(crate) fn range(version: Version, map: &'a SkipList<K, V, A, RC>, r: R) -> Self {
    Self(IterAll::range(version, map, r, false))
  }
}

impl<'a, K, V, A, RC, Q, R> Iter<'a, K, V, A, RC, Q, R>
where
  K: ?Sized + Type,
  K::Ref<'a>: KeyRef<'a, K>,
  V: ?Sized + Type,
  A: Allocator,
  RC: RefCounter,
  Q: ?Sized,
  R: RangeBounds<Q>,
{
  /// Returns the start bound of the iterator.
  #[inline]
  pub fn start_bound(&self) -> Bound<&Q> {
    self.0.start_bound()
  }

  /// Returns the end bound of the iterator.
  #[inline]
  pub fn end_bound(&self) -> Bound<&Q> {
    self.0.end_bound()
  }
}

impl<'a, K, V, A, RC, Q, R> Iter<'a, K, V, A, RC, Q, R>
where
  K: ?Sized + Type,
  K::Ref<'a>: KeyRef<'a, K>,
  V: ?Sized + Type,
  A: Allocator,
  RC: RefCounter,
  Q: ?Sized,
  R: RangeBounds<Q>,
{
  /// Returns the entry at the current head position of the iterator.
  #[inline]
  pub fn head(&self) -> Option<EntryRef<'a, K, V, A, RC>> {
    self.0.head().map(|e| EntryRef::<K, V, A, RC>(e.clone()))
  }

  /// Returns the entry at the current tail position of the iterator.
  #[inline]
  pub fn tail(&self) -> Option<EntryRef<'a, K, V, A, RC>> {
    self.0.tail().map(|e| EntryRef::<K, V, A, RC>(e.clone()))
  }
}

impl<'a, K, V, A, RC, Q, R> Iter<'a, K, V, A, RC, Q, R>
where
  K: ?Sized + Type,
  K::Ref<'a>: KeyRef<'a, K>,
  V: ?Sized + Type,
  A: Allocator,
  RC: RefCounter,
  Q: ?Sized + Comparable<K::Ref<'a>>,
  R: RangeBounds<Q>,
{
  /// Moves the iterator to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  ///
  /// **Note**: This method will clear the current state of the iterator.
  pub fn seek_upper_bound<QR>(&mut self, upper: Bound<&QR>) -> Option<EntryRef<'a, K, V, A, RC>>
  where
    QR: ?Sized + Comparable<K::Ref<'a>>,
  {
    self.0.seek_upper_bound(upper).map(EntryRef)
  }

  /// Moves the iterator to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  ///
  /// **Note**: This method will clear the current state of the iterator.
  pub(crate) fn seek_lower_bound<QR>(
    &mut self,
    lower: Bound<&QR>,
  ) -> Option<EntryRef<'a, K, V, A, RC>>
  where
    QR: ?Sized + Comparable<K::Ref<'a>>,
  {
    self.0.seek_lower_bound(lower).map(EntryRef)
  }
}

impl<'a, K, V, A, RC, Q, R> Iterator for Iter<'a, K, V, A, RC, Q, R>
where
  K: ?Sized + Type,
  K::Ref<'a>: KeyRef<'a, K>,
  V: ?Sized + Type,
  A: Allocator,
  RC: RefCounter,
  Q: ?Sized + Comparable<K::Ref<'a>>,
  R: RangeBounds<Q>,
{
  type Item = EntryRef<'a, K, V, A, RC>;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    self.0.next().map(EntryRef)
  }

  #[inline]
  fn last(self) -> Option<Self::Item>
  where
    Self: Sized,
  {
    self.0.last().map(EntryRef)
  }
}

impl<'a, K, V, A, RC, Q, R> DoubleEndedIterator for Iter<'a, K, V, A, RC, Q, R>
where
  K: ?Sized + Type,
  K::Ref<'a>: KeyRef<'a, K>,
  V: ?Sized + Type,
  A: Allocator,
  RC: RefCounter,
  Q: ?Sized + Comparable<K::Ref<'a>>,
  R: RangeBounds<Q>,
{
  fn next_back(&mut self) -> Option<Self::Item> {
    self.0.next_back().map(EntryRef)
  }
}
