use super::*;

/// An iterator over the skipmap. The current state of the iterator can be cloned by
/// simply value copying the struct.
pub struct Iter<'a, T, C, Q: ?Sized = &'static [u8], R = core::ops::RangeFull>(
  AllVersionsIter<'a, T, C, Q, R>,
);

impl<'a, R: Clone, Q: Clone, T: Clone, C> Clone for Iter<'a, T, C, Q, R> {
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<'a, R: Copy, Q: Copy, T: Copy, C> Copy for Iter<'a, T, C, Q, R> {}

impl<'a, T, C> Iter<'a, T, C>
where
  C: Comparator,
{
  #[inline]
  pub(crate) const fn new(version: u64, map: &'a SkipMap<T, C>) -> Self {
    Self(AllVersionsIter::new(version, map, false))
  }
}

impl<'a, Q, R, T, C> Iter<'a, T, C, Q, R>
where
  &'a [u8]: PartialOrd<Q>,
  Q: ?Sized + PartialOrd<&'a [u8]>,
{
  #[inline]
  pub(crate) fn range(version: u64, map: &'a SkipMap<T, C>, r: R) -> Self {
    Self(AllVersionsIter::range(version, map, r, false))
  }
}

impl<'a, Q: ?Sized, R, T, C> Iter<'a, T, C, Q, R> {
  /// Returns the bounds of the iterator.
  #[inline]
  pub const fn bounds(&self) -> &R {
    &self.0.range
  }
}

impl<'a, Q: ?Sized, R, T: Clone, C> Iter<'a, T, C, Q, R> {
  /// Returns the entry at the current position of the iterator.
  #[inline]
  pub fn entry(&self) -> Option<EntryRef<'a, T, C>> {
    self.0.last.clone().map(EntryRef)
  }
}

impl<'a, Q, R, T, C> Iter<'a, T, C, Q, R>
where
  C: Comparator,
  T: Trailer,
  &'a [u8]: PartialOrd<Q>,
  Q: ?Sized + PartialOrd<&'a [u8]>,
  R: RangeBounds<Q>,
{
  /// Moves the iterator to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  pub fn seek_upper_bound(&mut self, upper: Bound<&[u8]>) -> Option<EntryRef<'a, T, C>> {
    self.0.seek_upper_bound(upper).map(EntryRef)
  }

  /// Moves the iterator to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  pub fn seek_lower_bound(&mut self, lower: Bound<&[u8]>) -> Option<EntryRef<'a, T, C>> {
    self.0.seek_lower_bound(lower).map(EntryRef)
  }
}

impl<'a, Q, R, T, C> Iterator for Iter<'a, T, C, Q, R>
where
  C: Comparator,
  T: Trailer,
  &'a [u8]: PartialOrd<Q>,
  Q: ?Sized + PartialOrd<&'a [u8]>,
  R: RangeBounds<Q>,
{
  type Item = EntryRef<'a, T, C>;

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

  #[inline]
  fn max(self) -> Option<Self::Item>
  where
    Self: Sized,
    Self::Item: Ord,
  {
    self.last()
  }

  #[inline]
  fn min(self) -> Option<Self::Item>
  where
    Self: Sized,
    Self::Item: Ord,
  {
    self.0.min().map(EntryRef)
  }
}

impl<'a, Q, R, T, C> DoubleEndedIterator for Iter<'a, T, C, Q, R>
where
  C: Comparator,
  T: Trailer,
  &'a [u8]: PartialOrd<Q>,
  Q: ?Sized + PartialOrd<&'a [u8]>,
  R: RangeBounds<Q>,
{
  fn next_back(&mut self) -> Option<Self::Item> {
    self.0.next_back().map(EntryRef)
  }
}
