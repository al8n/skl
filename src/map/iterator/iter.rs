use super::*;

/// An iterator over the skipmap. The current state of the iterator can be cloned by
/// simply value copying the struct.
pub struct Iter<'a, C, T, Q: ?Sized = &'static [u8], R = core::ops::RangeFull>(
  AllVersionsIter<'a, C, T, Q, R>,
);

impl<'a, R: Clone, Q: Clone, T: Clone, C> Clone for Iter<'a, C, T, Q, R> {
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<'a, R: Copy, Q: Copy, T: Copy, C> Copy for Iter<'a, C, T, Q, R> {}

impl<'a, C, T> Iter<'a, C, T>
where
  C: Comparator,
{
  #[inline]
  pub(crate) const fn new(version: u56, map: &'a SkipMap<C, T>) -> Self {
    Self(AllVersionsIter::new(version, map, false))
  }
}

impl<'a, Q, R, C, T> Iter<'a, C, T, Q, R>
where
  &'a [u8]: PartialOrd<Q>,
  Q: ?Sized + PartialOrd<&'a [u8]>,
{
  #[inline]
  pub(crate) fn range(version: u56, map: &'a SkipMap<C, T>, r: R) -> Self {
    Self(AllVersionsIter::range(version, map, r, false))
  }
}

impl<'a, Q: ?Sized, R, C, T> Iter<'a, C, T, Q, R> {
  /// Returns the bounds of the iterator.
  #[inline]
  pub const fn bounds(&self) -> &R {
    &self.0.range
  }
}

impl<'a, Q: ?Sized, R, T: Clone, C> Iter<'a, C, T, Q, R> {
  /// Returns the entry at the current position of the iterator.
  #[inline]
  pub fn entry(&self) -> Option<EntryRef<'a, T>> {
    self.0.last.clone().map(EntryRef)
  }
}

impl<'a, Q, R, C, T> Iter<'a, C, T, Q, R>
where
  C: Comparator,
  T: Trailer,
  Q: ?Sized + Borrow<[u8]>,
  R: RangeBounds<Q>,
{
  /// Moves the iterator to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  pub fn seek_upper_bound(&mut self, upper: Bound<&[u8]>) -> Option<EntryRef<'a, T>> {
    self.0.seek_upper_bound(upper).map(EntryRef)
  }

  /// Moves the iterator to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  pub fn seek_lower_bound(&mut self, lower: Bound<&[u8]>) -> Option<EntryRef<'a, T>> {
    self.0.seek_lower_bound(lower).map(EntryRef)
  }
}

impl<'a, Q, R, C, T> Iterator for Iter<'a, C, T, Q, R>
where
  C: Comparator,
  T: Trailer,
  Q: ?Sized + Borrow<[u8]>,
  R: RangeBounds<Q>,
{
  type Item = EntryRef<'a, T>;

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

impl<'a, Q, R, C, T> DoubleEndedIterator for Iter<'a, C, T, Q, R>
where
  C: Comparator,
  T: Trailer,
  Q: ?Sized + Borrow<[u8]>,
  R: RangeBounds<Q>,
{
  fn next_back(&mut self) -> Option<Self::Item> {
    self.0.next_back().map(EntryRef)
  }
}
