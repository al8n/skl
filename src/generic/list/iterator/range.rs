use core::ops::{Bound, RangeBounds};

use dbutils::{
  equivalentor::{TypeRefComparator, TypeRefQueryComparator, TypeRefQueryRangeComparator},
  types::{LazyRef, Type},
};

use crate::{allocator::Node, generic::State, Transfer};

use super::super::{Allocator, EntryRef, NodePointer, RefCounter, SkipList, Version};

/// An iterator over the skipmap (this iterator will yields all versions). The current state of the iterator can be cloned by
/// simply value copying the struct.
pub struct Range<'a, K, V, S, C, A, RC, Q, R>
where
  A: Allocator,
  K: ?Sized + Type,
  V: ?Sized + Type,
  S: State,
  Q: ?Sized,
  RC: RefCounter,
{
  pub(super) map: &'a SkipList<K, V, C, A, RC>,
  pub(super) version: Version,
  pub(super) range: R,
  pub(super) all_versions: bool,
  pub(super) head: Option<EntryRef<'a, K, V, S, C, A, RC>>,
  pub(super) tail: Option<EntryRef<'a, K, V, S, C, A, RC>>,
  pub(super) _phantom: core::marker::PhantomData<Q>,
}

impl<'a, K, V, S, C, A, RC, Q, R: Clone> Clone for Range<'a, K, V, S, C, A, RC, Q, R>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  S: State,
  S::Data<'a, LazyRef<'a, V>>: Clone,
  A: Allocator,
  Q: ?Sized,
  RC: RefCounter,
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

impl<'a, K, V, S, C, A, RC, Q, R> Range<'a, K, V, S, C, A, RC, Q, R>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  S: State,
  A: Allocator,
  RC: RefCounter,
  Q: ?Sized,
{
  #[inline]
  pub(crate) fn new(
    version: Version,
    map: &'a SkipList<K, V, C, A, RC>,
    r: R,
    all_versions: bool,
  ) -> Self {
    Self {
      map,
      head: None,
      tail: None,
      version,
      range: r,
      all_versions,
      _phantom: core::marker::PhantomData,
    }
  }
}

impl<'a, K, V, S, C, A, RC, Q, R> Range<'a, K, V, S, C, A, RC, Q, R>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  S: State,
  A: Allocator,
  RC: RefCounter,
  R: RangeBounds<Q>,
  Q: ?Sized,
{
  /// Returns the start bound of the iterator.
  #[inline]
  pub fn start_bound(&self) -> Bound<&Q> {
    self.range.start_bound()
  }

  /// Returns the end bound of the iterator.
  #[inline]
  pub fn end_bound(&self) -> Bound<&Q> {
    self.range.end_bound()
  }

  /// Returns the entry at the current head position of the iterator.
  #[inline]
  pub const fn head(&self) -> Option<&EntryRef<'a, K, V, S, C, A, RC>> {
    self.head.as_ref()
  }

  /// Returns the entry at the current tail position of the iterator.
  #[inline]
  pub const fn tail(&self) -> Option<&EntryRef<'a, K, V, S, C, A, RC>> {
    self.tail.as_ref()
  }
}

impl<'a, K, V, S, C, A, RC, Q, R> Range<'a, K, V, S, C, A, RC, Q, R>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  S: Transfer<'a, LazyRef<'a, V>>,
  S::Data<'a, LazyRef<'a, V>>: Sized + Clone,
  A: Allocator,
  RC: RefCounter,
  Q: ?Sized,
  R: RangeBounds<Q>,
  C: TypeRefQueryComparator<'a, K, Q>,
{
  fn range_next_in(&mut self) -> Option<EntryRef<'a, K, V, S, C, A, RC>> {
    unsafe {
      let mut next_head = match self.head.as_ref() {
        Some(head) => self.map.get_next(head.ptr, 0),
        None => match self.range.start_bound() {
          Bound::Included(key) => self
            .map
            .find_near(self.version, key, false, true)
            .0
            .unwrap_or(<A::Node as Node>::Pointer::NULL),
          Bound::Excluded(key) => self
            .map
            .find_near(Version::MIN, key, false, false)
            .0
            .unwrap_or(<A::Node as Node>::Pointer::NULL),
          Bound::Unbounded => self.map.get_next(self.map.head, 0),
        },
      };

      self.head = if self.all_versions {
        self.map.move_to_next(&mut next_head, self.version, |nk| {
          self.map.cmp.query_compare_contains(&self.range, nk)
        })
      } else {
        self
          .map
          .move_to_next_maximum_version(&mut next_head, self.version, |nk| {
            if let Some(ref head) = self.head {
              !self.map.cmp.equivalent_refs(head.key(), nk)
                && self.map.cmp.query_compare_contains(&self.range, nk)
            } else {
              self.map.cmp.query_compare_contains(&self.range, nk)
            }
          })
      };

      if let Some(ref h) = self.head {
        match &self.tail {
          Some(t) => {
            let bound = Bound::Excluded(t.key());
            if !below_upper_bound(&self.map.cmp, &bound, h.key()) {
              self.head = None;
              self.tail = None;
            }
          }
          None => {
            let bound = self.range.end_bound();
            if !below_upper_bound_compare(&self.map.cmp, &bound, h.key()) {
              self.head = None;
              self.tail = None;
            }
          }
        }
      }

      self.head.clone()
    }
  }

  fn range_prev(&mut self) -> Option<EntryRef<'a, K, V, S, C, A, RC>> {
    unsafe {
      let mut next_tail = match self.tail.as_ref() {
        Some(tail) => self.map.get_prev(tail.ptr, 0),
        None => match self.range.end_bound() {
          Bound::Included(key) => self
            .map
            .find_near(Version::MIN, key, true, true)
            .0
            .unwrap_or(<A::Node as Node>::Pointer::NULL),
          Bound::Excluded(key) => self
            .map
            .find_near(self.version, key, true, false)
            .0
            .unwrap_or(<A::Node as Node>::Pointer::NULL),
          Bound::Unbounded => self.map.get_prev(self.map.tail, 0),
        },
      };

      self.tail = if self.all_versions {
        self.map.move_to_prev(&mut next_tail, self.version, |nk| {
          self.map.cmp.query_compare_contains(&self.range, nk)
        })
      } else {
        self
          .map
          .move_to_prev_maximum_version(&mut next_tail, self.version, |nk| {
            if let Some(ref tail) = self.tail {
              !self.map.cmp.equivalent_refs(tail.key(), nk)
                && self.map.cmp.query_compare_contains(&self.range, nk)
            } else {
              self.map.cmp.query_compare_contains(&self.range, nk)
            }
          })
      };

      if let Some(ref t) = self.tail {
        match &self.head {
          Some(h) => {
            let bound = Bound::Excluded(h.key());
            if !above_lower_bound(&self.map.cmp, &bound, t.key()) {
              self.head = None;
              self.tail = None;
            }
          }
          None => {
            let bound = self.range.start_bound();
            if !above_lower_bound_compare(&self.map.cmp, &bound, t.key()) {
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

impl<'a, K, V, S, C, A, RC, Q, R> Range<'a, K, V, S, C, A, RC, Q, R>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  S: Transfer<'a, LazyRef<'a, V>>,
  S::Data<'a, LazyRef<'a, V>>: Sized + Clone,
  A: Allocator,
  RC: RefCounter,
  Q: ?Sized,
  R: RangeBounds<Q>,
  C: TypeRefQueryComparator<'a, K, Q>,
{
  /// Moves the iterator to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  ///
  /// **Note:** This method will clear the current state of the iterator.
  pub fn seek_upper_bound<QR>(
    &mut self,
    upper: Bound<&QR>,
  ) -> Option<EntryRef<'a, K, V, S, C, A, RC>>
  where
    QR: ?Sized,
    C: TypeRefQueryComparator<'a, K, QR>,
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
  ) -> Option<EntryRef<'a, K, V, S, C, A, RC>>
  where
    QR: ?Sized,
    C: TypeRefQueryComparator<'a, K, QR>,
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
  fn seek_ge<QR>(&self, key: &QR) -> Option<EntryRef<'a, K, V, S, C, A, RC>>
  where
    QR: ?Sized,
    C: TypeRefQueryComparator<'a, K, QR>,
  {
    unsafe {
      let (n, _) = self.map.find_near(self.version, key, false, true);

      let mut n = n?;
      if n.is_null() || n.offset() == self.map.tail.offset() {
        return None;
      }

      if self.all_versions {
        self.map.move_to_next(&mut n, self.version, |nk| {
          self.map.cmp.query_compare_contains(&self.range, nk)
        })
      } else {
        self
          .map
          .move_to_next_maximum_version(&mut n, self.version, |nk| {
            self.map.cmp.query_compare_contains(&self.range, nk)
          })
      }
    }
  }

  /// Moves the iterator to the first entry whose key is greater than
  /// the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  fn seek_gt<QR>(&self, key: &QR) -> Option<EntryRef<'a, K, V, S, C, A, RC>>
  where
    QR: ?Sized,
    C: TypeRefQueryComparator<'a, K, QR>,
  {
    unsafe {
      let (n, _) = self.map.find_near(Version::MIN, key, false, false);

      let mut n = n?;
      if n.is_null() || n.offset() == self.map.tail.offset() {
        return None;
      }

      if self.all_versions {
        self.map.move_to_next(&mut n, self.version, |nk| {
          self.map.cmp.query_compare_contains(&self.range, nk)
        })
      } else {
        self
          .map
          .move_to_next_maximum_version(&mut n, self.version, |nk| {
            self.map.cmp.query_compare_contains(&self.range, nk)
          })
      }
    }
  }

  /// Moves the iterator to the first entry whose key is less than or
  /// equal to the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  fn seek_le<QR>(&self, key: &QR) -> Option<EntryRef<'a, K, V, S, C, A, RC>>
  where
    QR: ?Sized,
    C: TypeRefQueryComparator<'a, K, QR>,
  {
    unsafe {
      let (n, _) = self.map.find_near(Version::MIN, key, true, true); // find less or equal.

      let mut n = n?;
      if n.is_null() || n.offset() == self.map.head.offset() {
        return None;
      }

      if self.all_versions {
        self.map.move_to_prev(&mut n, self.version, |nk| {
          self.map.cmp.query_compare_contains(&self.range, nk)
        })
      } else {
        self
          .map
          .move_to_prev_maximum_version(&mut n, self.version, |nk| {
            self.map.cmp.query_compare_contains(&self.range, nk)
          })
      }
    }
  }

  /// Moves the iterator to the last entry whose key is less than the given
  /// key. Returns the key and value if the iterator is pointing at a valid entry,
  /// and `None` otherwise.
  fn seek_lt<QR>(&self, key: &QR) -> Option<EntryRef<'a, K, V, S, C, A, RC>>
  where
    QR: ?Sized,
    C: TypeRefQueryComparator<'a, K, QR>,
  {
    unsafe {
      let (n, _) = self.map.find_near(self.version, key, true, false); // find less or equal.

      let mut n = n?;
      if n.is_null() || n.offset() == self.map.head.offset() {
        return None;
      }

      if self.all_versions {
        self.map.move_to_prev(&mut n, self.version, |nk| {
          self.map.cmp.query_compare_contains(&self.range, nk)
        })
      } else {
        self
          .map
          .move_to_prev_maximum_version(&mut n, self.version, |nk| {
            self.map.cmp.query_compare_contains(&self.range, nk)
          })
      }
    }
  }

  #[inline]
  fn first(&mut self) -> Option<EntryRef<'a, K, V, S, C, A, RC>> {
    self.head = None;
    self.tail = None;
    self.next()
  }

  #[inline]
  fn last(&mut self) -> Option<EntryRef<'a, K, V, S, C, A, RC>> {
    self.tail = None;
    self.head = None;
    self.next_back()
  }
}

impl<'a, K, V, S, C, A, RC, Q, R> Iterator for Range<'a, K, V, S, C, A, RC, Q, R>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  S: Transfer<'a, LazyRef<'a, V>>,
  S::Data<'a, LazyRef<'a, V>>: Sized + Clone,
  A: Allocator,
  RC: RefCounter,
  Q: ?Sized,
  R: RangeBounds<Q>,
  C: TypeRefQueryComparator<'a, K, Q>,
{
  type Item = EntryRef<'a, K, V, S, C, A, RC>;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    self.range_next_in()
  }

  #[inline]
  fn last(mut self) -> Option<Self::Item>
  where
    Self: Sized,
  {
    Range::last(&mut self)
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

impl<'a, K, V, S, C, A, RC, Q, R> DoubleEndedIterator for Range<'a, K, V, S, C, A, RC, Q, R>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  S: Transfer<'a, LazyRef<'a, V>>,
  S::Data<'a, LazyRef<'a, V>>: Sized + Clone,
  A: Allocator,
  RC: RefCounter,
  Q: ?Sized,
  R: RangeBounds<Q>,
  C: TypeRefQueryComparator<'a, K, Q>,
{
  #[inline]
  fn next_back(&mut self) -> Option<Self::Item> {
    self.range_prev()
  }
}

/// Helper function to check if a value is above a lower bound
fn above_lower_bound_compare<'a, C, V, T>(cmp: &C, bound: &Bound<&T>, other: &V::Ref<'a>) -> bool
where
  V: ?Sized + Type,
  T: ?Sized,
  C: TypeRefQueryComparator<'a, V, T>,
{
  match *bound {
    Bound::Unbounded => true,
    Bound::Included(key) => cmp.query_compare_ref(other, key).is_ge(),
    Bound::Excluded(key) => cmp.query_compare_ref(other, key).is_gt(),
  }
}

/// Helper function to check if a value is above a lower bound
fn above_lower_bound<'a, C, K>(cmp: &C, bound: &Bound<&K::Ref<'a>>, other: &K::Ref<'a>) -> bool
where
  C: TypeRefComparator<'a, K>,
  K: ?Sized + Type,
{
  match *bound {
    Bound::Unbounded => true,
    Bound::Included(key) => cmp.compare_refs(key, other).is_le(),
    Bound::Excluded(key) => cmp.compare_refs(key, other).is_lt(),
  }
}

/// Helper function to check if a value is below an upper bound
fn below_upper_bound_compare<'a, C, V, T>(cmp: &C, bound: &Bound<&T>, other: &V::Ref<'a>) -> bool
where
  V: ?Sized + Type,
  T: ?Sized,
  C: TypeRefQueryComparator<'a, V, T>,
{
  match *bound {
    Bound::Unbounded => true,
    Bound::Included(key) => cmp.query_compare_ref(other, key).is_le(),
    Bound::Excluded(key) => cmp.query_compare_ref(other, key).is_lt(),
  }
}

/// Helper function to check if a value is below an upper bound
fn below_upper_bound<'a, C, K>(cmp: &C, bound: &Bound<&K::Ref<'a>>, other: &K::Ref<'a>) -> bool
where
  C: TypeRefComparator<'a, K>,
  K: ?Sized + Type,
{
  match *bound {
    Bound::Unbounded => true,
    Bound::Included(key) => cmp.compare_refs(key, other).is_ge(),
    Bound::Excluded(key) => cmp.compare_refs(key, other).is_gt(),
  }
}
