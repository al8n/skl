use core::ops::Bound;

use dbutils::{
  equivalentor::{TypeRefComparator, TypeRefQueryComparator},
  types::{LazyRef, Type},
};

use crate::{generic::State, Transfer};

use super::super::{Allocator, EntryRef, NodePointer, RefCounter, SkipList, Version};

/// An iterator over the skipmap (this iterator will yields all versions). The current state of the iterator can be cloned by
/// simply value copying the struct.
pub struct Iter<'a, K, V, S, C, A, R>
where
  A: Allocator,
  K: ?Sized + Type,
  V: ?Sized + Type,
  S: State,
  R: RefCounter,
{
  pub(super) map: &'a SkipList<K, V, C, A, R>,
  pub(super) version: Version,
  pub(super) all_versions: bool,
  pub(super) head: Option<EntryRef<'a, K, V, S, C, A, R>>,
  pub(super) tail: Option<EntryRef<'a, K, V, S, C, A, R>>,
}

impl<'a, K, V, S, C, A, R> Clone for Iter<'a, K, V, S, C, A, R>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  S: State,
  S::Data<'a, LazyRef<'a, V>>: Clone,
  A: Allocator,
  R: RefCounter,
{
  fn clone(&self) -> Self {
    Self {
      map: self.map,
      head: self.head.clone(),
      tail: self.tail.clone(),
      version: self.version,
      all_versions: self.all_versions,
    }
  }
}

impl<'a, K, V, S, C, A, R> Iter<'a, K, V, S, C, A, R>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  S: State,
  A: Allocator,
  R: RefCounter,
{
  #[inline]
  pub(crate) const fn new(
    version: Version,
    map: &'a SkipList<K, V, C, A, R>,
    all_versions: bool,
  ) -> Self {
    Self {
      map,
      head: None,
      tail: None,
      version,
      all_versions,
    }
  }
}

impl<'a, K, V, S, C, A, R> Iter<'a, K, V, S, C, A, R>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  S: State,
  A: Allocator,
  R: RefCounter,
{
  /// Returns the entry at the current head position of the iterator.
  #[inline]
  pub const fn head(&self) -> Option<&EntryRef<'a, K, V, S, C, A, R>> {
    self.head.as_ref()
  }

  /// Returns the entry at the current tail position of the iterator.
  #[inline]
  pub const fn tail(&self) -> Option<&EntryRef<'a, K, V, S, C, A, R>> {
    self.tail.as_ref()
  }
}

impl<'a, K, V, S, C, A, R> Iter<'a, K, V, S, C, A, R>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  S: Transfer<'a, LazyRef<'a, V>>,
  S::Data<'a, LazyRef<'a, V>>: Sized + Clone,
  A: Allocator,
  R: RefCounter,
  C: TypeRefComparator<'a, K>,
{
  /// Advances to the next position. Returns the key and value if the
  /// iterator is pointing at a valid entry, and `None` otherwise.
  fn next_in(&mut self) -> Option<EntryRef<'a, K, V, S, C, A, R>> {
    unsafe {
      let mut next_head = match self.head.as_ref() {
        Some(head) => self.map.get_next(head.ptr, 0),
        None => self.map.get_next(self.map.head, 0),
      };

      let next_head = if self.all_versions {
        self
          .map
          .move_to_next(&mut next_head, self.version, |_| true)
      } else {
        self
          .map
          .move_to_next_maximum_version(&mut next_head, self.version, |nk| {
            if let Some(ref head) = self.head {
              !self.map.cmp.equivalent_refs(head.key(), nk)
            } else {
              true
            }
          })
      };

      match (&next_head, &self.tail) {
        (Some(next), Some(t))
          if self
            .map
            .cmp
            .compare_refs(next.key(), t.key())
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
  fn prev(&mut self) -> Option<EntryRef<'a, K, V, S, C, A, R>> {
    unsafe {
      let mut next_tail = match self.tail.as_ref() {
        Some(tail) => self.map.get_prev(tail.ptr, 0),
        None => self.map.get_prev(self.map.tail, 0),
      };

      let next_tail = if self.all_versions {
        self
          .map
          .move_to_prev(&mut next_tail, self.version, |_| true)
      } else {
        self
          .map
          .move_to_prev_maximum_version(&mut next_tail, self.version, |nk| {
            if let Some(ref tail) = self.tail {
              !self.map.cmp.equivalent_refs(tail.key(), nk)
            } else {
              true
            }
          })
      };

      match (&self.head, &next_tail) {
        // The prev key is smaller than the latest head key we observed with this iterator.
        (Some(h), Some(next))
          if self
            .map
            .cmp
            .compare_refs(h.key(), next.key())
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
}

impl<'a, K, V, S, C, A, R> Iter<'a, K, V, S, C, A, R>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  S: Transfer<'a, LazyRef<'a, V>>,
  S::Data<'a, LazyRef<'a, V>>: Sized + Clone,
  A: Allocator,
  R: RefCounter,
  C: TypeRefComparator<'a, K>,
{
  /// Moves the iterator to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  ///
  /// **Note:** This method will clear the current state of the iterator.
  pub fn seek_upper_bound<QR>(
    &mut self,
    upper: Bound<&QR>,
  ) -> Option<EntryRef<'a, K, V, S, C, A, R>>
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
  ) -> Option<EntryRef<'a, K, V, S, C, A, R>>
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
  fn seek_ge<QR>(&self, key: &QR) -> Option<EntryRef<'a, K, V, S, C, A, R>>
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
        self.map.move_to_next(&mut n, self.version, |_| true)
      } else {
        self
          .map
          .move_to_next_maximum_version(&mut n, self.version, |_| true)
      }
    }
  }

  /// Moves the iterator to the first entry whose key is greater than
  /// the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  fn seek_gt<QR>(&self, key: &QR) -> Option<EntryRef<'a, K, V, S, C, A, R>>
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
        self.map.move_to_next(&mut n, self.version, |_| true)
      } else {
        self
          .map
          .move_to_next_maximum_version(&mut n, self.version, |_| true)
      }
    }
  }

  /// Moves the iterator to the first entry whose key is less than or
  /// equal to the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  fn seek_le<QR>(&self, key: &QR) -> Option<EntryRef<'a, K, V, S, C, A, R>>
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
        self.map.move_to_prev(&mut n, self.version, |_| true)
      } else {
        self
          .map
          .move_to_prev_maximum_version(&mut n, self.version, |_| true)
      }
    }
  }

  /// Moves the iterator to the last entry whose key is less than the given
  /// key. Returns the key and value if the iterator is pointing at a valid entry,
  /// and `None` otherwise.
  fn seek_lt<QR>(&self, key: &QR) -> Option<EntryRef<'a, K, V, S, C, A, R>>
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
        self.map.move_to_prev(&mut n, self.version, |_| true)
      } else {
        self
          .map
          .move_to_prev_maximum_version(&mut n, self.version, |_| true)
      }
    }
  }

  #[inline]
  fn first(&mut self) -> Option<EntryRef<'a, K, V, S, C, A, R>> {
    self.head = None;
    self.tail = None;
    self.next()
  }

  #[inline]
  fn last(&mut self) -> Option<EntryRef<'a, K, V, S, C, A, R>> {
    self.tail = None;
    self.head = None;
    self.prev()
  }
}

impl<'a, K, V, S, C, A, R> Iterator for Iter<'a, K, V, S, C, A, R>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  S: Transfer<'a, LazyRef<'a, V>>,
  S::Data<'a, LazyRef<'a, V>>: Sized + Clone,
  A: Allocator,
  R: RefCounter,
  C: TypeRefComparator<'a, K>,
{
  type Item = EntryRef<'a, K, V, S, C, A, R>;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    self.next_in()
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

impl<'a, K, V, S, C, A, R> DoubleEndedIterator for Iter<'a, K, V, S, C, A, R>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  S: Transfer<'a, LazyRef<'a, V>>,
  S::Data<'a, LazyRef<'a, V>>: Sized + Clone,
  A: Allocator,
  R: RefCounter,
  C: TypeRefComparator<'a, K>,
{
  #[inline]
  fn next_back(&mut self) -> Option<Self::Item> {
    self.prev()
  }
}
