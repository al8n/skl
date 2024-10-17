use core::ops::{Bound, RangeBounds, RangeFull};

use dbutils::{
  equivalent::Comparable,
  traits::{ComparableRangeBounds, KeyRef, Type},
};

use super::super::{Allocator, Node, NodePointer, SkipList, Version, VersionedEntryRef};

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
  pub(super) nd: <A::Node as Node>::Pointer,
  pub(super) version: Version,
  pub(super) range: R,
  pub(super) all_versions: bool,
  pub(super) last: Option<VersionedEntryRef<'a, K, V, A>>,
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
      nd: self.nd,
      version: self.version,
      range: self.range.clone(),
      last: self.last.clone(),
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
      nd: map.head,
      version,
      range: RangeFull,
      last: None,
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
      nd: map.head,
      version,
      range: r,
      last: None,
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
  /// Returns the bounds of the iterator.
  #[inline]
  pub const fn bounds(&self) -> &R {
    &self.range
  }

  /// Returns the entry at the current position of the iterator.
  #[inline]
  pub const fn entry(&self) -> Option<&VersionedEntryRef<'a, K, V, A>> {
    self.last.as_ref()
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
    self.nd = unsafe { self.map.get_next(self.nd, 0, false) };
    if self.all_versions {
      unsafe {
        self.map.move_to_next(&mut self.nd, self.version, |nk| {
          self.range.compare_contains(nk)
        })
      }
    } else {
      unsafe {
        self
          .map
          .move_to_next_max_version(&mut self.nd, self.version, |nk| {
            if let Some(ref last) = self.last {
              last.key().ne(nk) && self.range.compare_contains(nk)
            } else {
              self.range.compare_contains(nk)
            }
          })
      }
    }
    .inspect(|ent| {
      self.nd = ent.ptr;
      self.last = Some(ent.clone());
    })
  }

  /// Advances to the prev position. Returns the key and value if the
  /// iterator is pointing at a valid entry, and `None` otherwise.
  fn prev(&mut self) -> Option<VersionedEntryRef<'a, K, V, A>> {
    self.nd = unsafe { self.map.get_prev(self.nd, 0, !self.all_versions) };
    if self.all_versions {
      unsafe {
        self.map.move_to_prev(&mut self.nd, self.version, |nk| {
          self.range.compare_contains(nk)
        })
      }
    } else {
      unsafe {
        self
          .map
          .move_to_prev_max_version(&mut self.nd, self.version, |nk| {
            if let Some(ref last) = self.last {
              last.key().ne(nk) && self.range.compare_contains(nk)
            } else {
              self.range.compare_contains(nk)
            }
          })
      }
    }
    .inspect(|ent| {
      self.nd = ent.ptr;
      self.last = Some(ent.clone());
    })
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
  pub fn seek_upper_bound<QR>(
    &mut self,
    upper: Bound<&QR>,
  ) -> Option<VersionedEntryRef<'a, K, V, A>>
  where
    QR: ?Sized + Comparable<K::Ref<'a>>,
  {
    match upper {
      Bound::Included(key) => self.seek_le(key),
      Bound::Excluded(key) => self.seek_lt(key),
      Bound::Unbounded => self.last(),
    }
  }

  /// Moves the iterator to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  pub fn seek_lower_bound<QR>(
    &mut self,
    lower: Bound<&QR>,
  ) -> Option<VersionedEntryRef<'a, K, V, A>>
  where
    QR: ?Sized + Comparable<K::Ref<'a>>,
  {
    match lower {
      Bound::Included(key) => self.seek_ge(key),
      Bound::Excluded(key) => self.seek_gt(key),
      Bound::Unbounded => self.first(),
    }
  }

  /// Moves the iterator to the first entry whose key is greater than or
  /// equal to the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  fn seek_ge<QR>(&mut self, key: &QR) -> Option<VersionedEntryRef<'a, K, V, A>>
  where
    QR: ?Sized + Comparable<K::Ref<'a>>,
  {
    unsafe {
      let (n, _) = self
        .map
        .find_near(Version::MAX, key, false, true, !self.all_versions); // find the key with the max version.

      let mut n = n?;
      if n.is_null() || n.offset() == self.map.tail.offset() {
        return None;
      }

      if self.all_versions {
        self
          .map
          .move_to_next(&mut n, self.version, |nk| self.range.compare_contains(nk))
      } else {
        self
          .map
          .move_to_next_max_version(&mut n, self.version, |nk| self.range.compare_contains(nk))
      }
      .inspect(|ent| {
        self.nd = ent.ptr;
        self.last = Some(ent.clone());
      })
    }
  }

  /// Moves the iterator to the first entry whose key is greater than
  /// the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  fn seek_gt<QR>(&mut self, key: &QR) -> Option<VersionedEntryRef<'a, K, V, A>>
  where
    QR: ?Sized + Comparable<K::Ref<'a>>,
  {
    unsafe {
      let (n, _) = self
        .map
        .find_near(Version::MIN, key, false, false, !self.all_versions); // find the key with the max version.

      let mut n = n?;
      if n.is_null() || n.offset() == self.map.tail.offset() {
        return None;
      }

      if self.all_versions {
        self
          .map
          .move_to_next(&mut n, self.version, |nk| self.range.compare_contains(nk))
      } else {
        self
          .map
          .move_to_next_max_version(&mut n, self.version, |nk| self.range.compare_contains(nk))
      }
      .inspect(|ent| {
        self.nd = ent.ptr;
        self.last = Some(ent.clone());
      })
    }
  }

  /// Moves the iterator to the first entry whose key is less than or
  /// equal to the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  fn seek_le<QR>(&mut self, key: &QR) -> Option<VersionedEntryRef<'a, K, V, A>>
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
        self
          .map
          .move_to_prev(&mut n, self.version, |nk| self.range.compare_contains(nk))
      } else {
        self
          .map
          .move_to_prev_max_version(&mut n, self.version, |nk| self.range.compare_contains(nk))
      }
      .inspect(|ent| {
        self.nd = ent.ptr;
        self.last = Some(ent.clone());
      })
    }
  }

  /// Moves the iterator to the last entry whose key is less than the given
  /// key. Returns the key and value if the iterator is pointing at a valid entry,
  /// and `None` otherwise.
  fn seek_lt<QR>(&mut self, key: &QR) -> Option<VersionedEntryRef<'a, K, V, A>>
  where
    QR: ?Sized + Comparable<K::Ref<'a>>,
  {
    unsafe {
      let (n, _) = self
        .map
        .find_near(Version::MAX, key, true, false, !self.all_versions); // find less or equal.

      let mut n = n?;
      if n.is_null() || n.offset() == self.map.head.offset() {
        return None;
      }

      if self.all_versions {
        self
          .map
          .move_to_prev(&mut n, self.version, |nk| self.range.compare_contains(nk))
      } else {
        self
          .map
          .move_to_prev_max_version(&mut n, self.version, |nk| self.range.compare_contains(nk))
      }
      .inspect(|ent| {
        self.nd = ent.ptr;
        self.last = Some(ent.clone());
      })
    }
  }

  #[inline]
  fn first(&mut self) -> Option<VersionedEntryRef<'a, K, V, A>> {
    self.nd = self.map.head;
    self.last = None;
    self.next()
  }

  #[inline]
  fn last(&mut self) -> Option<VersionedEntryRef<'a, K, V, A>> {
    self.nd = self.map.tail;
    self.last = None;
    self.prev()
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
    self.next_in()
  }

  #[inline]
  fn last(mut self) -> Option<Self::Item>
  where
    Self: Sized,
  {
    self.seek_upper_bound::<K::Ref<'a>>(Bound::Unbounded)
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
    self.nd = self.map.head;
    self.next()
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
  fn next_back(&mut self) -> Option<Self::Item> {
    self.prev()
  }
}
