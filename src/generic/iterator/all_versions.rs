use super::{entry::VersionedEntryRef, *};
use dbutils::traits::ComparableRangeBounds;

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

  // /// Returns the entry at the current position of the iterator.
  // #[inline]
  // pub const fn entry(&self) -> Option<&VersionedEntryRef<'a, K, V, A>> {
  //   self.last.as_ref().map(|last| VersionedEntryRef::from)
  // }
}

impl<'a, K, V, A, Q, R> AllVersionsIter<'a, K, V, A, Q, R>
where
  K: ?Sized + Type,
  K::Ref<'a>: Ord,
  V: ?Sized + Type,
  A: Allocator,
  Q: ?Sized + Comparable<K::Ref<'a>>,
  R: RangeBounds<Q>,
{
  /// Advances to the next position. Returns the key and value if the
  /// iterator is pointing at a valid entry, and `None` otherwise.
  fn next_in(&mut self) -> Option<VersionedEntryRef<'a, K, V, A>> {
    loop {
      unsafe {
        self.nd = self.map.get_next(self.nd, 0, !self.all_versions);

        if self.nd.is_null() || self.nd.offset() == self.map.tail.offset() {
          return None;
        }

        let (value, pointer) = self.nd.get_value_and_trailer_with_pointer(&self.map.arena);
        if self.nd.version() > self.version {
          continue;
        }

        if !self.all_versions && value.is_none() {
          continue;
        }

        let nk = ty_ref::<K>(self.nd.get_key(&self.map.arena));
        if !self.all_versions {
          if let Some(ref last) = self.last {
            if Comparable::compare(last.key(), &nk) == cmp::Ordering::Equal {
              continue;
            }
          }
        }

        if self.range.compare_contains(&nk) {
          let ent = VersionedEntryRef::from_node_with_pointer(self.nd, &self.map.arena, pointer);
          self.last = Some(ent.clone());
          return Some(ent);
        }
      }
    }
  }

  /// Advances to the prev position. Returns the key and value if the
  /// iterator is pointing at a valid entry, and `None` otherwise.
  fn prev(&mut self) -> Option<VersionedEntryRef<'a, K, V, A>> {
    loop {
      unsafe {
        self.nd = self.map.get_prev(self.nd, 0, !self.all_versions);

        if self.nd.is_null() || self.nd.offset() == self.map.head.offset() {
          return None;
        }

        let (value, pointer) = self.nd.get_value_and_trailer_with_pointer(&self.map.arena);
        if self.nd.version() > self.version {
          continue;
        }

        if !self.all_versions && value.is_none() {
          continue;
        }

        let nk = ty_ref::<K>(self.nd.get_key(&self.map.arena));
        if !self.all_versions {
          if let Some(ref last) = self.last {
            if Comparable::compare(last.key(), &nk) == cmp::Ordering::Equal {
              continue;
            }
          }
        }

        if self.range.compare_contains(&nk) {
          let ent = VersionedEntryRef::from_node_with_pointer(self.nd, &self.map.arena, pointer);
          self.last = Some(ent.clone());
          return Some(ent);
        }
      }
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
  pub fn seek_upper_bound<QR>(
    &mut self,
    upper: Bound<&QR>,
  ) -> Option<VersionedEntryRef<'a, K, V, A>>
  where
    QR: ?Sized + Comparable<K::Ref<'a>>,
  {
    match upper {
      Bound::Included(key) => self.seek_le(key).map(|n| {
        let ent = VersionedEntryRef::from_node(n, &self.map.arena);
        self.last = Some(ent.clone());
        ent
      }),
      Bound::Excluded(key) => self.seek_lt(key).map(|n| {
        let ent = VersionedEntryRef::from_node(n, &self.map.arena);
        self.last = Some(ent.clone());
        ent
      }),
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
      Bound::Included(key) => self.seek_ge(key).map(|n| {
        let ent = VersionedEntryRef::from_node(n, &self.map.arena);
        self.last = Some(ent.clone());
        ent
      }),
      Bound::Excluded(key) => self.seek_gt(key).map(|n| {
        let ent = VersionedEntryRef::from_node(n, &self.map.arena);
        self.last = Some(ent.clone());
        ent
      }),
      Bound::Unbounded => self.first(),
    }
  }


  /// Moves the iterator to the first entry whose key is greater than or
  /// equal to the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  fn seek_ge<QR>(&mut self, key: &QR) -> Option<<A::Node as Node>::Pointer>
  where
    QR: ?Sized + Comparable<K::Ref<'a>>,
  {
    self.nd = self.map.ge(self.version, key, !self.all_versions)?;
    if self.nd.is_null() || self.nd.offset() == self.map.tail.offset() {
      return None;
    }

    loop {
      unsafe {
        // Safety: the nd is valid, we already check this
        // Safety: the node is allocated by the map's arena, so the key is valid
        let nk = ty_ref::<K>(self.nd.get_key(&self.map.arena));

        if self.range.compare_contains(&nk) {
          return Some(self.nd);
        } else {
          let upper = self.range.end_bound();
          match upper {
            Bound::Included(upper) => {
              if Comparable::compare(upper.borrow(), &nk).is_lt() {
                return None;
              }
            }
            Bound::Excluded(upper) => {
              if Comparable::compare(upper.borrow(), &nk).is_le() {
                return None;
              }
            }
            Bound::Unbounded => {}
          }

          self.nd = self.map.get_next(self.nd, 0, !self.all_versions);
        }
      }
    }
  }

  /// Moves the iterator to the first entry whose key is greater than
  /// the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  fn seek_gt<QR>(&mut self, key: &QR) -> Option<<A::Node as Node>::Pointer>
  where
    QR: ?Sized + Comparable<K::Ref<'a>>,
  {
    self.nd = self.map.gt(self.version, key, self.all_versions)?;

    if self.nd.is_null() || self.nd.offset() == self.map.tail.offset() {
      return None;
    }

    loop {
      unsafe {
        // Safety: the nd is valid, we already check this
        // Safety: the node is allocated by the map's arena, so the key is valid
        let nk = ty_ref::<K>(self.nd.get_key(&self.map.arena));

        if self.range.compare_contains(&nk) {
          return Some(self.nd);
        } else {
          let upper = self.range.end_bound();
          match upper {
            Bound::Included(upper) => {
              if Comparable::compare(upper.borrow(), &nk).is_lt() {
                return None;
              }
            }
            Bound::Excluded(upper) => {
              if Comparable::compare(upper.borrow(), &nk).is_le() {
                return None;
              }
            }
            Bound::Unbounded => {}
          }

          self.nd = self.map.get_next(self.nd, 0, !self.all_versions);
        }
      }
    }
  }

  /// Moves the iterator to the first entry whose key is less than or
  /// equal to the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  fn seek_le<QR>(&mut self, key: &QR) -> Option<<A::Node as Node>::Pointer>
  where
    QR: ?Sized + Comparable<K::Ref<'a>>,
  {
    self.nd = self.map.le(self.version, key, self.all_versions)?;

    loop {
      unsafe {
        // Safety: the node is allocated by the map's arena, so the key is valid
        let nk = ty_ref::<K>(self.nd.get_key(&self.map.arena));

        if self.range.compare_contains(&nk) {
          return Some(self.nd);
        } else {
          let lower = self.range.start_bound();
          match lower {
            Bound::Included(lower) => {
              if Comparable::compare(lower.borrow(), &nk).is_gt() {
                return None;
              }
            }
            Bound::Excluded(lower) => {
              if Comparable::compare(lower.borrow(), &nk).is_ge() {
                return None;
              }
            }
            Bound::Unbounded => {}
          }

          self.nd = self.map.get_prev(self.nd, 0, !self.all_versions);
        }
      }
    }
  }

  /// Moves the iterator to the last entry whose key is less than the given
  /// key. Returns the key and value if the iterator is pointing at a valid entry,
  /// and `None` otherwise.
  fn seek_lt<QR>(&mut self, key: &QR) -> Option<<A::Node as Node>::Pointer>
  where
    QR: ?Sized + Comparable<K::Ref<'a>>,
  {
    // NB: the top-level AllVersionsIter has already adjusted key based on
    // the upper-bound.
    self.nd = self.map.lt(self.version, key, self.all_versions)?;

    loop {
      unsafe {
        // Safety: the node is allocated by the map's arena, so the key is valid
        let nk = ty_ref::<K>(self.nd.get_key(&self.map.arena));

        if self.range.compare_contains(&nk) {
          return Some(self.nd);
        } else {
          let lower = self.range.start_bound();
          match lower {
            Bound::Included(lower) => {
              if Comparable::compare(lower.borrow(), &nk).is_gt() {
                return None;
              }
            }
            Bound::Excluded(lower) => {
              if Comparable::compare(lower.borrow(), &nk).is_ge() {
                return None;
              }
            }
            Bound::Unbounded => {}
          }

          self.nd = self.map.get_prev(self.nd, 0, !self.all_versions);
        }
      }
    }
  }

  /// Seeks position at the first entry in map. Returns the key and value
  /// if the iterator is pointing at a valid entry, and `None` otherwise.
  fn first(&mut self) -> Option<VersionedEntryRef<'a, K, V, A>> {
    self.nd = self.map.first_in(self.version, self.all_versions)?;

    loop {
      if self.nd.is_null() || self.nd.offset() == self.map.tail.offset() {
        return None;
      }

      unsafe {
        let nk = ty_ref::<K>(self.nd.get_key(&self.map.arena));
        let (value, pointer) = self.nd.get_value_and_trailer_with_pointer(&self.map.arena);

        if self.nd.version() > self.version {
          self.nd = self.map.get_next(self.nd, 0, !self.all_versions);
          continue;
        }

        if !self.all_versions && value.is_none() {
          self.nd = self.map.get_next(self.nd, 0, !self.all_versions);
          continue;
        }

        if self.range.compare_contains(&nk) {
          let ent = VersionedEntryRef::from_node_with_pointer(self.nd, &self.map.arena, pointer);
          self.last = Some(ent.clone());
          return Some(ent);
        }

        self.nd = self.map.get_next(self.nd, 0, !self.all_versions);
      }
    }
  }

  /// Seeks position at the last entry in the iterator. Returns the key and value if
  /// the iterator is pointing at a valid entry, and `None` otherwise.
  fn last(&mut self) -> Option<VersionedEntryRef<'a, K, V, A>> {
    self.nd = self.map.last_in(self.version, self.all_versions)?;

    loop {
      unsafe {
        if self.nd.is_null() || self.nd.offset() == self.map.head.offset() {
          return None;
        }

        let (value, pointer) = self.nd.get_value_and_trailer_with_pointer(&self.map.arena);

        if self.nd.version() > self.version {
          self.nd = self.map.get_prev(self.nd, 0, !self.all_versions);
          continue;
        }

        if !self.all_versions && value.is_none() {
          self.nd = self.map.get_prev(self.nd, 0, !self.all_versions);
          continue;
        }

        let nk = ty_ref::<K>(self.nd.get_key(&self.map.arena));
        if self.range.compare_contains(&nk) {
          let ent = VersionedEntryRef::from_node_with_pointer(self.nd, &self.map.arena, pointer);
          return Some(ent);
        }

        self.nd = self.map.get_prev(self.nd, 0, !self.all_versions);
      }
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
    self.next_in().map(|v| {
      // Safety: the EntryRef holds a reference to the map, so it is always valid.
      unsafe { core::mem::transmute(v) }
    })
  }

  #[inline]
  fn last(mut self) -> Option<Self::Item>
  where
    Self: Sized,
  {
    self
      .seek_upper_bound::<K::Ref<'a>>(Bound::Unbounded)
      .map(|e| {
        // Safety: the EntryRef holds a reference to the map, so it is always valid.
        unsafe { core::mem::transmute(e) }
      })
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
    self.first().map(|e| {
      // Safety: the EntryRef holds a reference to the map, so it is always valid.
      unsafe { core::mem::transmute(e) }
    })
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
    self.prev().map(|v| {
      // Safety: the EntryRef holds a reference to the map, so it is always valid.
      unsafe { core::mem::transmute(v) }
    })
  }
}
