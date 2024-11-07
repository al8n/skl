use core::{
  borrow::Borrow,
  ops::{Bound, RangeBounds},
};

use dbutils::equivalentor::Comparator;

use super::{
  super::{Allocator, EntryRef, SkipList, Version},
  IterAll,
};

/// An iterator over the skipmap. The current state of the iterator can be cloned by
/// simply value copying the struct.
pub struct Iter<'a, C, A: Allocator, Q = [u8], R = core::ops::RangeFull>(IterAll<'a, C, A, Q, R>)
where
  A: Allocator,
  Q: ?Sized;

impl<C, A, R: Clone, Q> Clone for Iter<'_, C, A, Q, R>
where
  A: Allocator,
  Q: ?Sized,
{
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<'a, A, C> Iter<'a, C, A>
where
  A: Allocator,
{
  #[inline]
  pub(crate) const fn new(version: Version, map: &'a SkipList<A, C>) -> Self {
    Self(IterAll::new(version, map, false))
  }
}

impl<'a, C, A, Q, R> Iter<'a, C, A, Q, R>
where
  A: Allocator,
  Q: ?Sized,
{
  #[inline]
  pub(crate) fn range(version: Version, map: &'a SkipList<A, C>, r: R) -> Self {
    Self(IterAll::range(version, map, r, false))
  }
}

impl<C, A, Q, R> Iter<'_, C, A, Q, R>
where
  A: Allocator,
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

impl<'a, C, A, Q, R> Iter<'a, C, A, Q, R>
where
  A: Allocator,
  Q: ?Sized,
  R: RangeBounds<Q>,
{
  /// Returns the entry at the current head position of the iterator.
  #[inline]
  pub fn head(&self) -> Option<EntryRef<'a, A, C>> {
    self.0.head().map(|e| EntryRef::<A, C>(*e))
  }

  /// Returns the entry at the current tail position of the iterator.
  #[inline]
  pub fn tail(&self) -> Option<EntryRef<'a, A, C>> {
    self.0.tail().map(|e| EntryRef::<A, C>(*e))
  }
}

impl<'a, C, A, Q, R> Iter<'a, C, A, Q, R>
where
  A: Allocator,
  Q: ?Sized + Borrow<[u8]>,
  C: Comparator,
  R: RangeBounds<Q>,
{
  /// Moves the iterator to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  ///
  /// **Note**: This method will clear the current state of the iterator.
  pub fn seek_upper_bound<QR>(&mut self, upper: Bound<&QR>) -> Option<EntryRef<'a, A, C>>
  where
    QR: ?Sized + Borrow<[u8]>,
  {
    self.0.seek_upper_bound(upper).map(EntryRef)
  }

  /// Moves the iterator to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  ///
  /// **Note**: This method will clear the current state of the iterator.
  pub(crate) fn seek_lower_bound<QR>(&mut self, lower: Bound<&QR>) -> Option<EntryRef<'a, A, C>>
  where
    QR: ?Sized + Borrow<[u8]>,
  {
    self.0.seek_lower_bound(lower).map(EntryRef)
  }
}

impl<'a, C, A, Q, R> Iterator for Iter<'a, C, A, Q, R>
where
  A: Allocator,
  C: Comparator,
  Q: ?Sized + Borrow<[u8]>,
  R: RangeBounds<Q>,
{
  type Item = EntryRef<'a, A, C>;

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

impl<C, A, Q, R> DoubleEndedIterator for Iter<'_, C, A, Q, R>
where
  A: Allocator,
  Q: ?Sized + Borrow<[u8]>,
  C: Comparator,
  R: RangeBounds<Q>,
{
  fn next_back(&mut self) -> Option<Self::Item> {
    self.0.next_back().map(EntryRef)
  }
}
