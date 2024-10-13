use entry::EntryRef;

use super::*;

/// An iterator over the skipmap. The current state of the iterator can be cloned by
/// simply value copying the struct.
pub struct Iter<'a, K, V, A: Allocator, Q = <K as Type>::Ref<'a>, R = core::ops::RangeFull>(
  AllVersionsIter<'a, K, V, A, Q, R>,
)
where
  A: Allocator,
  K: ?Sized + Type,
  V: ?Sized + Type,
  Q: ?Sized;

impl<K, V, A, R: Clone, Q> Clone for Iter<'_, K, V, A, Q, R>
where
  A: Allocator,
  K: ?Sized + Type,
  V: ?Sized + Type,
  Q: ?Sized,
{
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<K, V, A, R: Copy, Q> Copy for Iter<'_, K, V, A, Q, R>
where
  A: Allocator,
  K: ?Sized + Type,
  V: ?Sized + Type,
  Q: ?Sized,
{
}

impl<'a, K, V, A> Iter<'a, K, V, A>
where
  K: ?Sized + Type,
  K::Ref<'a>: KeyRef<'a, K>,
  V: ?Sized + Type,
  A: Allocator,
{
  #[inline]
  pub(crate) const fn new(version: Version, map: &'a SkipList<K, V, A>) -> Self {
    Self(AllVersionsIter::new(version, map, false))
  }
}

impl<'a, K, V, A, Q, R> Iter<'a, K, V, A, Q, R>
where
  K: ?Sized + Type,
  K::Ref<'a>: KeyRef<'a, K>,
  V: ?Sized + Type,
  A: Allocator,
  Q: ?Sized,
{
  #[inline]
  pub(crate) fn range(version: Version, map: &'a SkipList<K, V, A>, r: R) -> Self {
    Self(AllVersionsIter::range(version, map, r, false))
  }
}

impl<'a, K, V, A, Q, R> Iter<'a, K, V, A, Q, R>
where
  K: ?Sized + Type,
  K::Ref<'a>: KeyRef<'a, K>,
  V: ?Sized + Type,
  A: Allocator,
  Q: ?Sized,
{
  /// Returns the bounds of the iterator.
  #[inline]
  pub const fn bounds(&self) -> &R {
    &self.0.range
  }
}

impl<'a, K, V, A, Q, R> Iter<'a, K, V, A, Q, R>
where
  K: ?Sized + Type,
  K::Ref<'a>: KeyRef<'a, K>,
  V: ?Sized + Type,
  A: Allocator,
  Q: ?Sized,
{
  // /// Returns the entry at the current position of the iterator.
  // #[inline]
  // pub fn entry(&self) -> Option<EntryRef<'a, K, V, A>> {
  //   self.0.last.map(EntryRef::<K, V, A>)
  // }
}

impl<'a, K, V, A, Q, R> Iter<'a, K, V, A, Q, R>
where
  K: ?Sized + Type,
  K::Ref<'a>: KeyRef<'a, K>,
  V: ?Sized + Type,
  A: Allocator,
  Q: ?Sized + Ord + Comparable<K::Ref<'a>>,
  R: RangeBounds<Q>,
{
  /// Moves the iterator to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  pub fn seek_upper_bound<QR>(&mut self, upper: Bound<&QR>) -> Option<EntryRef<'a, K, V, A>>
  where
    QR: ?Sized + Ord + Comparable<K::Ref<'a>>,
  {
    self.0.seek_upper_bound(upper).map(EntryRef)
  }

  /// Moves the iterator to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  pub fn seek_lower_bound<QR>(&mut self, lower: Bound<&QR>) -> Option<EntryRef<'a, K, V, A>>
  where
    QR: ?Sized + Ord + Comparable<K::Ref<'a>>,
  {
    self.0.seek_lower_bound(lower).map(EntryRef)
  }
}

impl<'a, K, V, A, Q, R> Iterator for Iter<'a, K, V, A, Q, R>
where
  K: ?Sized + Type,
  K::Ref<'a>: KeyRef<'a, K>,
  V: ?Sized + Type,
  A: Allocator,
  Q: ?Sized + Ord + Comparable<K::Ref<'a>>,
  R: RangeBounds<Q>,
{
  type Item = EntryRef<'a, K, V, A>;

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

impl<'a, K, V, A, Q, R> DoubleEndedIterator for Iter<'a, K, V, A, Q, R>
where
  K: ?Sized + Type,
  K::Ref<'a>: KeyRef<'a, K>,
  V: ?Sized + Type,
  A: Allocator,
  Q: ?Sized + Ord + Comparable<K::Ref<'a>>,
  R: RangeBounds<Q>,
{
  fn next_back(&mut self) -> Option<Self::Item> {
    self.0.next_back().map(EntryRef)
  }
}
