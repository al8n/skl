use core::ops::{Bound, RangeBounds};

use dbutils::{
  equivalent::Comparable,
  traits::{ComparableRangeBounds, KeyRef, Type},
};

use crate::allocator::Node;

use super::super::{Allocator, NodePointer, SkipList, Version, VersionedEntryRef};

/// An iterator over the skipmap. The current state of the iterator can be cloned by
/// simply value copying the struct.
pub struct AllVersionsIter<'a, K, V, A, Q = <K as Type>::Ref<'a>, R = core::ops::RangeFull>
where
  A: Allocator,
  K: ?Sized + Type,
  V: ?Sized + Type,
  Q: ?Sized,
{
  pub(super) map: &'a SkipList<K, V, A>,
  pub(super) version: Version,
  pub(super) range: Option<R>,
  pub(super) all_versions: bool,
  pub(super) head: Option<VersionedEntryRef<'a, K, V, A>>,
  pub(super) tail: Option<VersionedEntryRef<'a, K, V, A>>,
  pub(super) _phantom: core::marker::PhantomData<Q>,
}

impl<'a, K, V, A, Q, R: Clone> Clone for AllVersionsIter<'a, K, V, A, Q, R>
where
  K: ?Sized + Type,
  K::Ref<'a>: Clone,
  V: ?Sized + Type,
  A: Allocator,
  Q: ?Sized,
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

impl<'a, K, V, A, Q, R: Copy> Copy for AllVersionsIter<'a, K, V, A, Q, R>
where
  K: ?Sized + Type,
  K::Ref<'a>: Copy,
  V: ?Sized + Type,
  A: Allocator,
  VersionedEntryRef<'a, K, V, A>: Copy,
  Q: ?Sized,
{
}

impl<'a, K, V, A> AllVersionsIter<'a, K, V, A>
where
  K: ?Sized + Type,
  K::Ref<'a>: KeyRef<'a, K>,
  V: ?Sized + Type,
  A: Allocator,
{
  #[inline]
  pub(crate) const fn new(
    version: Version,
    map: &'a SkipList<K, V, A>,
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

impl<'a, K, V, A, Q, R> AllVersionsIter<'a, K, V, A, Q, R>
where
  K: ?Sized + Type,
  K::Ref<'a>: KeyRef<'a, K>,
  V: ?Sized + Type,
  A: Allocator,
  Q: ?Sized,
{
  #[inline]
  pub(crate) fn range(
    version: Version,
    map: &'a SkipList<K, V, A>,
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

impl<'a, K, V, A, Q, R> AllVersionsIter<'a, K, V, A, Q, R>
where
  K: ?Sized + Type,
  K::Ref<'a>: KeyRef<'a, K>,
  V: ?Sized + Type,
  A: Allocator,
  R: RangeBounds<Q>,
  Q: ?Sized,
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
  pub const fn head(&self) -> Option<&VersionedEntryRef<'a, K, V, A>> {
    self.head.as_ref()
  }

  /// Returns the entry at the current tail position of the iterator.
  #[inline]
  pub const fn tail(&self) -> Option<&VersionedEntryRef<'a, K, V, A>> {
    self.tail.as_ref()
  }
}

impl<'a, K, V, A, Q, R> AllVersionsIter<'a, K, V, A, Q, R>
where
  K: ?Sized + Type,
  K::Ref<'a>: KeyRef<'a, K>,
  V: ?Sized + Type,
  A: Allocator,
  Q: ?Sized + Comparable<K::Ref<'a>>,
  R: RangeBounds<Q>,
{
  /// Advances to the next position. Returns the key and value if the
  /// iterator is pointing at a valid entry, and `None` otherwise.
  fn next_in(&mut self) -> Option<VersionedEntryRef<'a, K, V, A>> {
    unsafe {
      let mut next_head = match self.head.as_ref() {
        Some(head) => self.map.get_next(head.ptr, 0, !self.all_versions),
        None => self.map.get_next(self.map.head, 0, !self.all_versions),
      };

      let next_head = if self.all_versions {
        self
          .map
          .move_to_next(&mut next_head, self.version, |nk| self.check_bounds(nk))
      } else {
        self
          .map
          .move_to_next_max_version(&mut next_head, self.version, |nk| {
            if let Some(ref head) = self.head {
              head.key().ne(nk) && self.check_bounds(nk)
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
          self.head = next_head.clone();
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
  fn prev(&mut self) -> Option<VersionedEntryRef<'a, K, V, A>> {
    unsafe {
      let mut next_tail = match self.tail.as_ref() {
        Some(tail) => self.map.get_prev(tail.ptr, 0, !self.all_versions),
        None => self.map.get_prev(self.map.tail, 0, !self.all_versions),
      };

      let next_tail = if self.all_versions {
        self
          .map
          .move_to_prev(&mut next_tail, self.version, |nk| self.check_bounds(nk))
      } else {
        self
          .map
          .move_to_prev_max_version(&mut next_tail, self.version, |nk| {
            if let Some(ref tail) = self.tail {
              tail.key().ne(nk) && self.check_bounds(nk)
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
          self.tail = next_tail.clone();
          next_tail
        }
        (_, None) => {
          self.tail = next_tail;
          None
        }
      }
    }
  }

  fn range_next_in(&mut self) -> Option<VersionedEntryRef<'a, K, V, A>> {
    unsafe {
      let mut next_head = match self.head.as_ref() {
        Some(head) => self.map.get_next(head.ptr, 0, !self.all_versions),
        None => match self.range.as_ref().unwrap().start_bound() {
          Bound::Included(key) => self
            .map
            .find_near(self.version, key, false, true, !self.all_versions)
            .0
            .unwrap_or(<A::Node as Node>::Pointer::NULL),
          Bound::Excluded(key) => self
            .map
            .find_near(Version::MIN, key, false, false, !self.all_versions)
            .0
            .unwrap_or(<A::Node as Node>::Pointer::NULL),
          Bound::Unbounded => self.map.get_next(self.map.head, 0, !self.all_versions),
        },
      };

      self.head = if self.all_versions {
        self
          .map
          .move_to_next(&mut next_head, self.version, |nk| self.check_bounds(nk))
      } else {
        self
          .map
          .move_to_next_max_version(&mut next_head, self.version, |nk| {
            if let Some(ref head) = self.head {
              head.key().ne(nk) && self.check_bounds(nk)
            } else {
              self.check_bounds(nk)
            }
          })
      };

      if let Some(ref h) = self.head {
        match &self.tail {
          Some(t) => {
            let bound = Bound::Excluded(t.key());
            if !below_upper_bound(&bound, h.key()) {
              self.head = None;
              self.tail = None;
            }
          }
          None => {
            let bound = self.range.as_ref().unwrap().end_bound();
            if !below_upper_bound_compare(&bound, h.key()) {
              self.head = None;
              self.tail = None;
            }
          }
        }
      }

      self.head.clone()
    }
  }

  fn range_prev(&mut self) -> Option<VersionedEntryRef<'a, K, V, A>> {
    unsafe {
      let mut next_tail = match self.tail.as_ref() {
        Some(tail) => self.map.get_prev(tail.ptr, 0, !self.all_versions),
        None => match self.range.as_ref().unwrap().end_bound() {
          Bound::Included(key) => self
            .map
            .find_near(Version::MIN, key, true, true, !self.all_versions)
            .0
            .unwrap_or(<A::Node as Node>::Pointer::NULL),
          Bound::Excluded(key) => self
            .map
            .find_near(self.version, key, true, false, !self.all_versions)
            .0
            .unwrap_or(<A::Node as Node>::Pointer::NULL),
          Bound::Unbounded => self.map.get_prev(self.map.tail, 0, !self.all_versions),
        },
      };

      self.tail = if self.all_versions {
        self
          .map
          .move_to_prev(&mut next_tail, self.version, |nk| self.check_bounds(nk))
      } else {
        self
          .map
          .move_to_prev_max_version(&mut next_tail, self.version, |nk| {
            if let Some(ref tail) = self.tail {
              tail.key().ne(nk) && self.check_bounds(nk)
            } else {
              self.check_bounds(nk)
            }
          })
      };

      if let Some(ref t) = self.tail {
        match &self.head {
          Some(h) => {
            let bound = Bound::Excluded(h.key());
            if !above_lower_bound(&bound, t.key()) {
              self.head = None;
              self.tail = None;
            }
          }
          None => {
            let bound = self.range.as_ref().unwrap().start_bound();
            if !above_lower_bound_compare(&bound, t.key()) {
              self.head = None;
              self.tail = None;
            }
          }
        }
      }

      self.tail.clone()
    }
  }
}

impl<'a, K, V, A, Q, R> AllVersionsIter<'a, K, V, A, Q, R>
where
  K: ?Sized + Type,
  K::Ref<'a>: KeyRef<'a, K>,
  V: ?Sized + Type,
  A: Allocator,
  Q: ?Sized + Comparable<K::Ref<'a>>,
  R: RangeBounds<Q>,
{
  /// Moves the iterator to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  ///
  /// **Note:** This method will clear the current state of the iterator.
  pub fn seek_upper_bound<QR>(
    &mut self,
    upper: Bound<&QR>,
  ) -> Option<VersionedEntryRef<'a, K, V, A>>
  where
    QR: ?Sized + Comparable<K::Ref<'a>>,
  {
    self.head = None;
    self.tail = None;

    match upper {
      Bound::Included(key) => self.seek_le(key).inspect(|ent| {
        self.head = Some(ent.clone());
      }),
      Bound::Excluded(key) => self.seek_lt(key).inspect(|ent| {
        self.head = Some(ent.clone());
      }),
      Bound::Unbounded => self.last(),
    }
  }

  /// Moves the iterator to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  ///
  /// **Note:** This method will clear the current state of the iterator.
  pub fn seek_lower_bound<QR>(
    &mut self,
    lower: Bound<&QR>,
  ) -> Option<VersionedEntryRef<'a, K, V, A>>
  where
    QR: ?Sized + Comparable<K::Ref<'a>>,
  {
    self.head = None;
    self.tail = None;

    match lower {
      Bound::Included(key) => self.seek_ge(key).inspect(|ent| {
        self.head = Some(ent.clone());
      }),
      Bound::Excluded(key) => self.seek_gt(key).inspect(|ent| {
        self.head = Some(ent.clone());
      }),
      Bound::Unbounded => self.first(),
    }
  }

  /// Moves the iterator to the first entry whose key is greater than or
  /// equal to the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  fn seek_ge<QR>(&self, key: &QR) -> Option<VersionedEntryRef<'a, K, V, A>>
  where
    QR: ?Sized + Comparable<K::Ref<'a>>,
  {
    unsafe {
      let (n, _) = self
        .map
        .find_near(self.version, key, false, true, !self.all_versions);

      let mut n = n?;
      if n.is_null() || n.offset() == self.map.tail.offset() {
        return None;
      }

      if self.all_versions {
        self.map.move_to_next(&mut n, self.version, |nk| {
          if let Some(ref range) = self.range {
            range.compare_contains(nk)
          } else {
            true
          }
        })
      } else {
        self
          .map
          .move_to_next_max_version(&mut n, self.version, |nk| {
            if let Some(ref range) = self.range {
              range.compare_contains(nk)
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
  fn seek_gt<QR>(&self, key: &QR) -> Option<VersionedEntryRef<'a, K, V, A>>
  where
    QR: ?Sized + Comparable<K::Ref<'a>>,
  {
    unsafe {
      let (n, _) = self
        .map
        .find_near(Version::MIN, key, false, false, !self.all_versions);

      let mut n = n?;
      if n.is_null() || n.offset() == self.map.tail.offset() {
        return None;
      }

      if self.all_versions {
        self.map.move_to_next(&mut n, self.version, |nk| {
          if let Some(ref range) = self.range {
            range.compare_contains(nk)
          } else {
            true
          }
        })
      } else {
        self
          .map
          .move_to_next_max_version(&mut n, self.version, |nk| {
            if let Some(ref range) = self.range {
              range.compare_contains(nk)
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
  fn seek_le<QR>(&self, key: &QR) -> Option<VersionedEntryRef<'a, K, V, A>>
  where
    QR: ?Sized + Comparable<K::Ref<'a>>,
  {
    unsafe {
      let (n, _) = self
        .map
        .find_near(Version::MIN, key, true, true, !self.all_versions); // find less or equal.

      let mut n = n?;
      if n.is_null() || n.offset() == self.map.head.offset() {
        return None;
      }

      if self.all_versions {
        self.map.move_to_prev(&mut n, self.version, |nk| {
          if let Some(ref range) = self.range {
            range.compare_contains(nk)
          } else {
            true
          }
        })
      } else {
        self
          .map
          .move_to_prev_max_version(&mut n, self.version, |nk| {
            if let Some(ref range) = self.range {
              range.compare_contains(nk)
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
  fn seek_lt<QR>(&self, key: &QR) -> Option<VersionedEntryRef<'a, K, V, A>>
  where
    QR: ?Sized + Comparable<K::Ref<'a>>,
  {
    unsafe {
      let (n, _) = self
        .map
        .find_near(self.version, key, true, false, !self.all_versions); // find less or equal.

      let mut n = n?;
      if n.is_null() || n.offset() == self.map.head.offset() {
        return None;
      }

      if self.all_versions {
        self.map.move_to_prev(&mut n, self.version, |nk| {
          if let Some(ref range) = self.range {
            range.compare_contains(nk)
          } else {
            true
          }
        })
      } else {
        self
          .map
          .move_to_prev_max_version(&mut n, self.version, |nk| self.check_bounds(nk))
      }
    }
  }

  #[inline]
  fn first(&mut self) -> Option<VersionedEntryRef<'a, K, V, A>> {
    self.head = None;
    self.tail = None;
    self.next()
  }

  #[inline]
  fn last(&mut self) -> Option<VersionedEntryRef<'a, K, V, A>> {
    self.tail = None;
    self.head = None;
    self.prev()
  }

  #[inline]
  fn check_bounds(&self, nk: &K::Ref<'a>) -> bool {
    if let Some(ref range) = self.range {
      range.compare_contains(nk)
    } else {
      true
    }
  }
}

impl<'a, K, V, A, Q, R> Iterator for AllVersionsIter<'a, K, V, A, Q, R>
where
  K: ?Sized + Type,
  K::Ref<'a>: KeyRef<'a, K>,
  V: ?Sized + Type,
  A: Allocator,
  Q: ?Sized + Comparable<K::Ref<'a>>,
  R: RangeBounds<Q>,
{
  type Item = VersionedEntryRef<'a, K, V, A>;

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
    AllVersionsIter::last(&mut self)
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

impl<'a, K, V, A, Q, R> DoubleEndedIterator for AllVersionsIter<'a, K, V, A, Q, R>
where
  K: ?Sized + Type,
  K::Ref<'a>: KeyRef<'a, K>,
  V: ?Sized + Type,
  A: Allocator,
  Q: ?Sized + Comparable<K::Ref<'a>>,
  R: RangeBounds<Q>,
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
fn above_lower_bound_compare<V, T: ?Sized + Comparable<V>>(bound: &Bound<&T>, other: &V) -> bool {
  match *bound {
    Bound::Unbounded => true,
    Bound::Included(key) => key.compare(other).is_le(),
    Bound::Excluded(key) => key.compare(other).is_lt(),
  }
}

/// Helper function to check if a value is above a lower bound
fn above_lower_bound<K: ?Sized + Ord>(bound: &Bound<&K>, other: &K) -> bool {
  match *bound {
    Bound::Unbounded => true,
    Bound::Included(key) => key.cmp(other).is_le(),
    Bound::Excluded(key) => key.cmp(other).is_lt(),
  }
}

/// Helper function to check if a value is below an upper bound
fn below_upper_bound_compare<V: ?Sized, T: ?Sized + Comparable<V>>(
  bound: &Bound<&T>,
  other: &V,
) -> bool {
  match *bound {
    Bound::Unbounded => true,
    Bound::Included(key) => key.compare(other).is_ge(),
    Bound::Excluded(key) => key.compare(other).is_gt(),
  }
}

/// Helper function to check if a value is below an upper bound
fn below_upper_bound<K: ?Sized + Ord>(bound: &Bound<&K>, other: &K) -> bool {
  match *bound {
    Bound::Unbounded => true,
    Bound::Included(key) => key.cmp(other).is_ge(),
    Bound::Excluded(key) => key.cmp(other).is_gt(),
  }
}
