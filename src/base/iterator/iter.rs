use super::*;

/// An iterator over the skipmap. The current state of the iterator can be cloned by
/// simply value copying the struct.
pub struct Iter<'a, A: Allocator, C, Q: ?Sized = &'static [u8], R = core::ops::RangeFull>(
  AllVersionsIter<'a, A, C, Q, R>,
);

impl<A: Allocator, C, R: Clone, Q: Clone> Clone for Iter<'_, A, C, Q, R> {
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<A: Allocator, C, R: Copy, Q: Copy> Copy for Iter<'_, A, C, Q, R> {}

impl<'a, A, C> Iter<'a, A, C>
where
  A: Allocator,
  C: Comparator,
{
  #[inline]
  pub(crate) const fn new(version: Version, map: &'a SkipList<A, C>) -> Self {
    Self(AllVersionsIter::new(version, map, false))
  }
}

impl<'a, A, C, Q, R> Iter<'a, A, C, Q, R>
where
  A: Allocator,
  Q: ?Sized + Borrow<[u8]>,
{
  #[inline]
  pub(crate) fn range(version: Version, map: &'a SkipList<A, C>, r: R) -> Self {
    Self(AllVersionsIter::range(version, map, r, false))
  }
}

impl<A, C, Q: ?Sized, R> Iter<'_, A, C, Q, R>
where
  A: Allocator,
{
  /// Returns the bounds of the iterator.
  #[inline]
  pub const fn bounds(&self) -> &R {
    &self.0.range
  }
}

impl<'a, A, C, Q: ?Sized, R> Iter<'a, A, C, Q, R>
where
  A: Allocator,
{
  /// Returns the entry at the current position of the iterator.
  #[inline]
  pub fn entry(&self) -> Option<EntryRef<'a, A>> {
    self.0.last.map(EntryRef)
  }
}

impl<'a, A, C, Q, R> Iter<'a, A, C, Q, R>
where
  A: Allocator,
  C: Comparator,
  Q: ?Sized + Borrow<[u8]>,
  R: RangeBounds<Q>,
{
  /// Moves the iterator to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  pub fn seek_upper_bound(&mut self, upper: Bound<&[u8]>) -> Option<EntryRef<'a, A>> {
    self.0.seek_upper_bound(upper).map(EntryRef)
  }

  /// Moves the iterator to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  pub fn seek_lower_bound(&mut self, lower: Bound<&[u8]>) -> Option<EntryRef<'a, A>> {
    self.0.seek_lower_bound(lower).map(EntryRef)
  }
}

impl<'a, A, C, Q, R> Iterator for Iter<'a, A, C, Q, R>
where
  A: Allocator,
  C: Comparator,
  Q: ?Sized + Borrow<[u8]>,
  R: RangeBounds<Q>,
{
  type Item = EntryRef<'a, A>;

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

impl<A, C, Q, R> DoubleEndedIterator for Iter<'_, A, C, Q, R>
where
  A: Allocator,
  C: Comparator,
  Q: ?Sized + Borrow<[u8]>,
  R: RangeBounds<Q>,
{
  fn next_back(&mut self) -> Option<Self::Item> {
    self.0.next_back().map(EntryRef)
  }
}
