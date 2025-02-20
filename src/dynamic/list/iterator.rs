use super::{Allocator, EntryRef, NodePointer, RefCounter, SkipList, Version};
use crate::{allocator::Node, State, Transfer};
use core::{
  borrow::Borrow,
  ops::{Bound, RangeBounds},
};
use dbutils::equivalentor::{BytesComparator, BytesRangeComparator};

/// An iterator over the skipmap (this iterator will yields all versions). The current state of the iterator can be cloned by
/// simply value copying the struct.
pub struct Iter<'a, S, C, A, RC, Q = [u8], R = core::ops::RangeFull>
where
  A: Allocator,
  RC: RefCounter,
  Q: ?Sized,
  S: State,
{
  pub(super) map: &'a SkipList<C, A, RC>,
  pub(super) version: Version,
  pub(super) range: Option<R>,
  pub(super) all_versions: bool,
  pub(super) head: Option<EntryRef<'a, S, C, A, RC>>,
  pub(super) tail: Option<EntryRef<'a, S, C, A, RC>>,
  pub(super) _phantom: core::marker::PhantomData<Q>,
}

impl<'a, S, C, A, RC, Q, R> Clone for Iter<'a, S, C, A, RC, Q, R>
where
  A: Allocator,
  RC: RefCounter,
  Q: ?Sized,
  R: Clone,
  S: State,
  S::Data<'a, &'a [u8]>: Clone,
{
  fn clone(&self) -> Self {
    Self {
      map: self.map,
      head: self.head.clone(),
      tail: self.tail.clone(),
      version: self.version,
      range: self.range.clone(),
      all_versions: self.all_versions,
      _phantom: core::marker::PhantomData,
    }
  }
}

impl<'a, S, C, A, RC, Q, R> Copy for Iter<'a, S, C, A, RC, Q, R>
where
  A: Allocator,
  RC: RefCounter,
  Q: ?Sized,
  R: Copy,
  S: State,
  S::Data<'a, &'a [u8]>: Copy,
{
}

impl<'a, S, C, A, RC> Iter<'a, S, C, A, RC>
where
  A: Allocator,
  RC: RefCounter,
  S: State,
{
  #[inline]
  pub(crate) const fn new(
    version: Version,
    map: &'a SkipList<C, A, RC>,
    all_versions: bool,
  ) -> Self {
    Self {
      map,
      head: None,
      tail: None,
      version,
      range: None,
      all_versions,
      _phantom: core::marker::PhantomData,
    }
  }
}

impl<'a, S, C, A, RC, Q, R> Iter<'a, S, C, A, RC, Q, R>
where
  A: Allocator,
  RC: RefCounter,
  Q: ?Sized,
  S: State,
{
  #[inline]
  pub(crate) fn range(
    version: Version,
    map: &'a SkipList<C, A, RC>,
    r: R,
    all_versions: bool,
  ) -> Self {
    Self {
      map,
      head: None,
      tail: None,
      version,
      range: Some(r),
      all_versions,
      _phantom: core::marker::PhantomData,
    }
  }
}

impl<'a, S, C, A, RC, Q, R> Iter<'a, S, C, A, RC, Q, R>
where
  A: Allocator,
  RC: RefCounter,
  R: RangeBounds<Q>,
  Q: ?Sized,
  S: State,
{
  /// Returns the start bound of the iterator.
  #[inline]
  pub fn start_bound(&self) -> Bound<&Q> {
    self
      .range
      .as_ref()
      .map(|r| r.start_bound())
      .unwrap_or(Bound::Unbounded)
  }

  /// Returns the end bound of the iterator.
  #[inline]
  pub fn end_bound(&self) -> Bound<&Q> {
    self
      .range
      .as_ref()
      .map(|r| r.end_bound())
      .unwrap_or(Bound::Unbounded)
  }

  /// Returns the entry at the current head position of the iterator.
  #[inline]
  pub const fn head(&self) -> Option<&EntryRef<'a, S, C, A, RC>> {
    self.head.as_ref()
  }

  /// Returns the entry at the current tail position of the iterator.
  #[inline]
  pub const fn tail(&self) -> Option<&EntryRef<'a, S, C, A, RC>> {
    self.tail.as_ref()
  }
}

impl<'a, S, C, A, RC, Q, R> Iter<'a, S, C, A, RC, Q, R>
where
  A: Allocator,
  C: BytesComparator,
  RC: RefCounter,
  Q: ?Sized + Borrow<[u8]>,
  R: RangeBounds<Q>,
  S: Transfer<'a, &'a [u8]>,
  S::Data<'a, &'a [u8]>: Copy,
{
  /// Advances to the next position. Returns the key and value if the
  /// iterator is pointing at a valid entry, and `None` otherwise.
  fn next_in(&mut self) -> Option<EntryRef<'a, S, C, A, RC>> {
    unsafe {
      let mut next_head = match self.head.as_ref() {
        Some(head) => self.map.get_next(head.ptr, 0),
        None => self.map.get_next(self.map.head, 0),
      };

      let next_head = if self.all_versions {
        self
          .map
          .move_to_next(&mut next_head, self.version, |nk| self.check_bounds(nk))
      } else {
        self
          .map
          .move_to_next_maximum_version(&mut next_head, self.version, |nk| {
            if let Some(ref head) = self.head {
              !self.map.cmp.equivalent(head.key(), nk) && self.check_bounds(nk)
            } else {
              self.check_bounds(nk)
            }
          })
      };

      match (&next_head, &self.tail) {
        (Some(next), Some(t))
          if next
            .key()
            .cmp(t.key())
            .then_with(|| t.version.cmp(&next.version))
            .is_ge() =>
        {
          self.head = next_head;
          None
        }
        (Some(_), _) => {
          self.head = next_head;
          next_head
        }
        (None, _) => {
          self.head = next_head;
          None
        }
      }
    }
  }

  /// Advances to the prev position. Returns the key and value if the
  /// iterator is pointing at a valid entry, and `None` otherwise.
  fn prev(&mut self) -> Option<EntryRef<'a, S, C, A, RC>> {
    unsafe {
      let mut next_tail = match self.tail.as_ref() {
        Some(tail) => self.map.get_prev(tail.ptr, 0),
        None => self.map.get_prev(self.map.tail, 0),
      };

      let next_tail = if self.all_versions {
        self
          .map
          .move_to_prev(&mut next_tail, self.version, |nk| self.check_bounds(nk))
      } else {
        self
          .map
          .move_to_prev_maximum_version(&mut next_tail, self.version, |nk| {
            if let Some(ref tail) = self.tail {
              !self.map.cmp.equivalent(tail.key(), nk) && self.check_bounds(nk)
            } else {
              self.check_bounds(nk)
            }
          })
      };

      match (&self.head, &next_tail) {
        // The prev key is smaller than the latest head key we observed with this iterator.
        (Some(h), Some(next))
          if h
            .key()
            .cmp(next.key())
            .then_with(|| h.version.cmp(&next.version))
            .is_ge() =>
        {
          self.tail = next_tail;
          None
        }
        (_, Some(_)) => {
          self.tail = next_tail;
          next_tail
        }
        (_, None) => {
          self.tail = next_tail;
          None
        }
      }
    }
  }

  fn range_next_in(&mut self) -> Option<EntryRef<'a, S, C, A, RC>> {
    unsafe {
      let mut next_head = match self.head.as_ref() {
        Some(head) => self.map.get_next(head.ptr, 0),
        None => match self.range.as_ref().unwrap().start_bound() {
          Bound::Included(key) => self
            .map
            .find_near(self.version, key.borrow(), false, true)
            .0
            .unwrap_or(<A::Node as Node>::Pointer::NULL),
          Bound::Excluded(key) => self
            .map
            .find_near(Version::MIN, key.borrow(), false, false)
            .0
            .unwrap_or(<A::Node as Node>::Pointer::NULL),
          Bound::Unbounded => self.map.get_next(self.map.head, 0),
        },
      };

      self.head = if self.all_versions {
        self
          .map
          .move_to_next(&mut next_head, self.version, |nk| self.check_bounds(nk))
      } else {
        self
          .map
          .move_to_next_maximum_version(&mut next_head, self.version, |nk| {
            if let Some(ref head) = self.head {
              !self.map.cmp.equivalent(head.key(), nk) && self.check_bounds(nk)
            } else {
              self.check_bounds(nk)
            }
          })
      };

      if let Some(ref h) = self.head {
        match &self.tail {
          Some(t) => {
            let bound = Bound::Excluded(t.key());
            if !below_upper_bound(&self.map.cmp, bound, h.key()) {
              self.head = None;
              self.tail = None;
            }
          }
          None => {
            let bound = self.range.as_ref().unwrap().end_bound().map(|b| b.borrow());
            if !below_upper_bound_compare(&self.map.cmp, bound, h.key()) {
              self.head = None;
              self.tail = None;
            }
          }
        }
      }

      self.head
    }
  }

  fn range_prev(&mut self) -> Option<EntryRef<'a, S, C, A, RC>> {
    unsafe {
      let mut next_tail = match self.tail.as_ref() {
        Some(tail) => self.map.get_prev(tail.ptr, 0),
        None => match self.range.as_ref().unwrap().end_bound() {
          Bound::Included(key) => self
            .map
            .find_near(Version::MIN, key.borrow(), true, true)
            .0
            .unwrap_or(<A::Node as Node>::Pointer::NULL),
          Bound::Excluded(key) => self
            .map
            .find_near(self.version, key.borrow(), true, false)
            .0
            .unwrap_or(<A::Node as Node>::Pointer::NULL),
          Bound::Unbounded => self.map.get_prev(self.map.tail, 0),
        },
      };

      self.tail = if self.all_versions {
        self
          .map
          .move_to_prev(&mut next_tail, self.version, |nk| self.check_bounds(nk))
      } else {
        self
          .map
          .move_to_prev_maximum_version(&mut next_tail, self.version, |nk| {
            if let Some(ref tail) = self.tail {
              !self.map.cmp.equivalent(tail.key(), nk) && self.check_bounds(nk)
            } else {
              self.check_bounds(nk)
            }
          })
      };

      if let Some(ref t) = self.tail {
        match &self.head {
          Some(h) => {
            let bound = Bound::Excluded(h.key());
            if !above_lower_bound(&self.map.cmp, bound, t.key()) {
              self.head = None;
              self.tail = None;
            }
          }
          None => {
            let bound = self
              .range
              .as_ref()
              .unwrap()
              .start_bound()
              .map(|b| b.borrow());
            if !above_lower_bound_compare(&self.map.cmp, bound, t.key()) {
              self.head = None;
              self.tail = None;
            }
          }
        }
      }

      self.tail
    }
  }
}

impl<'a, S, C, A, RC, Q, R> Iter<'a, S, C, A, RC, Q, R>
where
  A: Allocator,
  C: BytesComparator,
  RC: RefCounter,
  Q: ?Sized + Borrow<[u8]>,
  R: RangeBounds<Q>,
  S: Transfer<'a, &'a [u8]>,
  S::Data<'a, &'a [u8]>: Copy,
{
  /// Moves the iterator to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  ///
  /// **Note:** This method will clear the current state of the iterator.
  pub fn seek_upper_bound<QR>(&mut self, upper: Bound<&QR>) -> Option<EntryRef<'a, S, C, A, RC>>
  where
    QR: ?Sized + Borrow<[u8]>,
  {
    self.head = None;
    self.tail = None;

    match upper {
      Bound::Included(key) => self.seek_le(key).inspect(|ent| {
        self.head = Some(*ent);
      }),
      Bound::Excluded(key) => self.seek_lt(key).inspect(|ent| {
        self.head = Some(*ent);
      }),
      Bound::Unbounded => self.last(),
    }
  }

  /// Moves the iterator to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  ///
  /// **Note:** This method will clear the current state of the iterator.
  pub fn seek_lower_bound<QR>(&mut self, lower: Bound<&QR>) -> Option<EntryRef<'a, S, C, A, RC>>
  where
    QR: ?Sized + Borrow<[u8]>,
  {
    self.head = None;
    self.tail = None;

    match lower {
      Bound::Included(key) => self.seek_ge(key).inspect(|ent| {
        self.head = Some(*ent);
      }),
      Bound::Excluded(key) => self.seek_gt(key).inspect(|ent| {
        self.head = Some(*ent);
      }),
      Bound::Unbounded => self.first(),
    }
  }

  /// Moves the iterator to the first entry whose key is greater than or
  /// equal to the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  fn seek_ge<QR>(&self, key: &QR) -> Option<EntryRef<'a, S, C, A, RC>>
  where
    QR: ?Sized + Borrow<[u8]>,
  {
    unsafe {
      let (n, _) = self.map.find_near(self.version, key.borrow(), false, true);

      let mut n = n?;
      if n.is_null() || n.offset() == self.map.tail.offset() {
        return None;
      }

      if self.all_versions {
        self.map.move_to_next(&mut n, self.version, |nk| {
          if let Some(ref range) = self.range {
            self.map.cmp.compare_contains(range, nk)
          } else {
            true
          }
        })
      } else {
        self
          .map
          .move_to_next_maximum_version(&mut n, self.version, |nk| {
            if let Some(ref range) = self.range {
              self.map.cmp.compare_contains(range, nk)
            } else {
              true
            }
          })
      }
    }
  }

  /// Moves the iterator to the first entry whose key is greater than
  /// the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  fn seek_gt<QR>(&self, key: &QR) -> Option<EntryRef<'a, S, C, A, RC>>
  where
    QR: ?Sized + Borrow<[u8]>,
  {
    unsafe {
      let (n, _) = self.map.find_near(Version::MIN, key.borrow(), false, false);

      let mut n = n?;
      if n.is_null() || n.offset() == self.map.tail.offset() {
        return None;
      }

      if self.all_versions {
        self.map.move_to_next(&mut n, self.version, |nk| {
          if let Some(ref range) = self.range {
            self.map.cmp.compare_contains(range, nk)
          } else {
            true
          }
        })
      } else {
        self
          .map
          .move_to_next_maximum_version(&mut n, self.version, |nk| {
            if let Some(ref range) = self.range {
              self.map.cmp.compare_contains(range, nk)
            } else {
              true
            }
          })
      }
    }
  }

  /// Moves the iterator to the first entry whose key is less than or
  /// equal to the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  fn seek_le<QR>(&self, key: &QR) -> Option<EntryRef<'a, S, C, A, RC>>
  where
    QR: ?Sized + Borrow<[u8]>,
  {
    unsafe {
      let (n, _) = self.map.find_near(Version::MIN, key.borrow(), true, true); // find less or equal.

      let mut n = n?;
      if n.is_null() || n.offset() == self.map.head.offset() {
        return None;
      }

      if self.all_versions {
        self.map.move_to_prev(&mut n, self.version, |nk| {
          if let Some(ref range) = self.range {
            self.map.cmp.compare_contains(range, nk)
          } else {
            true
          }
        })
      } else {
        self
          .map
          .move_to_prev_maximum_version(&mut n, self.version, |nk| {
            if let Some(ref range) = self.range {
              self.map.cmp.compare_contains(range, nk)
            } else {
              true
            }
          })
      }
    }
  }

  /// Moves the iterator to the last entry whose key is less than the given
  /// key. Returns the key and value if the iterator is pointing at a valid entry,
  /// and `None` otherwise.
  fn seek_lt<QR>(&self, key: &QR) -> Option<EntryRef<'a, S, C, A, RC>>
  where
    QR: ?Sized + Borrow<[u8]>,
  {
    unsafe {
      let (n, _) = self.map.find_near(self.version, key.borrow(), true, false); // find less or equal.

      let mut n = n?;
      if n.is_null() || n.offset() == self.map.head.offset() {
        return None;
      }

      if self.all_versions {
        self.map.move_to_prev(&mut n, self.version, |nk| {
          if let Some(ref range) = self.range {
            self.map.cmp.compare_contains(range, nk)
          } else {
            true
          }
        })
      } else {
        self
          .map
          .move_to_prev_maximum_version(&mut n, self.version, |nk| self.check_bounds(nk))
      }
    }
  }

  #[inline]
  fn first(&mut self) -> Option<EntryRef<'a, S, C, A, RC>> {
    self.head = None;
    self.tail = None;
    self.next()
  }

  #[inline]
  fn last(&mut self) -> Option<EntryRef<'a, S, C, A, RC>> {
    self.tail = None;
    self.head = None;
    self.prev()
  }

  #[inline]
  fn check_bounds(&self, nk: &[u8]) -> bool {
    if let Some(ref range) = self.range {
      self.map.cmp.compare_contains(range, nk)
    } else {
      true
    }
  }
}

impl<'a, S, C, A, RC, Q, R> Iterator for Iter<'a, S, C, A, RC, Q, R>
where
  A: Allocator,
  C: BytesComparator,
  RC: RefCounter,
  Q: ?Sized + Borrow<[u8]>,
  R: RangeBounds<Q>,
  S: Transfer<'a, &'a [u8]>,
  S::Data<'a, &'a [u8]>: Copy,
{
  type Item = EntryRef<'a, S, C, A, RC>;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    if self.range.is_some() {
      self.range_next_in()
    } else {
      self.next_in()
    }
  }

  #[inline]
  fn last(mut self) -> Option<Self::Item>
  where
    Self: Sized,
  {
    Iter::last(&mut self)
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
  fn min(mut self) -> Option<Self::Item>
  where
    Self: Sized,
    Self::Item: Ord,
  {
    self.first()
  }
}

impl<'a, S, C, A, RC, Q, R> DoubleEndedIterator for Iter<'a, S, C, A, RC, Q, R>
where
  A: Allocator,
  C: BytesComparator,
  RC: RefCounter,
  Q: ?Sized + Borrow<[u8]>,
  R: RangeBounds<Q>,
  S: Transfer<'a, &'a [u8]>,
  S::Data<'a, &'a [u8]>: Copy,
{
  #[inline]
  fn next_back(&mut self) -> Option<Self::Item> {
    if self.range.is_some() {
      self.range_prev()
    } else {
      self.prev()
    }
  }
}

/// Helper function to check if a value is above a lower bound
fn above_lower_bound_compare<C: BytesComparator>(
  cmp: &C,
  bound: Bound<&[u8]>,
  other: &[u8],
) -> bool {
  match bound {
    Bound::Unbounded => true,
    Bound::Included(key) => cmp.compare(key, other).is_le(),
    Bound::Excluded(key) => cmp.compare(key, other).is_lt(),
  }
}

/// Helper function to check if a value is above a lower bound
fn above_lower_bound<C: BytesComparator>(cmp: &C, bound: Bound<&[u8]>, other: &[u8]) -> bool {
  match bound {
    Bound::Unbounded => true,
    Bound::Included(key) => cmp.compare(key, other).is_le(),
    Bound::Excluded(key) => cmp.compare(key, other).is_lt(),
  }
}

/// Helper function to check if a value is below an upper bound
fn below_upper_bound_compare<C: BytesComparator>(
  cmp: &C,
  bound: Bound<&[u8]>,
  other: &[u8],
) -> bool {
  match bound {
    Bound::Unbounded => true,
    Bound::Included(key) => cmp.compare(key, other).is_ge(),
    Bound::Excluded(key) => cmp.compare(key, other).is_gt(),
  }
}

/// Helper function to check if a value is below an upper bound
fn below_upper_bound<C: BytesComparator>(cmp: &C, bound: Bound<&[u8]>, other: &[u8]) -> bool {
  match bound {
    Bound::Unbounded => true,
    Bound::Included(key) => cmp.compare(key, other).is_ge(),
    Bound::Excluded(key) => cmp.compare(key, other).is_gt(),
  }
}
