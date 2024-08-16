use super::*;

/// An iterator over the skipmap. The current state of the iterator can be cloned by
/// simply value copying the struct.
pub struct AllVersionsIter<'a, C, T, Q: ?Sized = &'static [u8], R = core::ops::RangeFull> {
  pub(super) map: &'a SkipMap<C, T>,
  pub(super) nd: NodePtr<T>,
  pub(super) version: u56,
  pub(super) range: R,
  pub(super) all_versions: bool,
  pub(super) last: Option<VersionedEntryRef<'a, T>>,
  pub(super) _phantom: core::marker::PhantomData<Q>,
}

impl<'a, R: Clone, Q: Clone, T: Clone, C> Clone for AllVersionsIter<'a, C, T, Q, R> {
  fn clone(&self) -> Self {
    Self {
      map: self.map,
      nd: self.nd,
      version: self.version,
      range: self.range.clone(),
      last: self.last,
      all_versions: self.all_versions,
      _phantom: core::marker::PhantomData,
    }
  }
}

impl<'a, R: Copy, Q: Copy, T: Copy, C> Copy for AllVersionsIter<'a, C, T, Q, R> {}

impl<'a, C, T> AllVersionsIter<'a, C, T>
where
  C: Comparator,
{
  #[inline]
  pub(crate) const fn new(version: u56, map: &'a SkipMap<C, T>, all_versions: bool) -> Self {
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

impl<'a, Q, R, C, T> AllVersionsIter<'a, C, T, Q, R>
where
  &'a [u8]: PartialOrd<Q>,
  Q: ?Sized + PartialOrd<&'a [u8]>,
{
  #[inline]
  pub(crate) fn range(version: u56, map: &'a SkipMap<C, T>, r: R, all_versions: bool) -> Self {
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

impl<'a, Q: ?Sized, R, C, T> AllVersionsIter<'a, C, T, Q, R> {
  /// Returns the bounds of the iterator.
  #[inline]
  pub const fn bounds(&self) -> &R {
    &self.range
  }

  /// Returns the entry at the current position of the iterator.
  #[inline]
  pub const fn entry(&self) -> Option<&VersionedEntryRef<'a, T>> {
    self.last.as_ref()
  }
}

impl<'a, Q, R, C, T> AllVersionsIter<'a, C, T, Q, R>
where
  C: Comparator,
  T: Trailer,
  Q: ?Sized + Borrow<[u8]>,
  R: RangeBounds<Q>,
{
  /// Moves the iterator to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  pub fn seek_upper_bound(&mut self, upper: Bound<&[u8]>) -> Option<VersionedEntryRef<'a, T>> {
    match upper {
      Bound::Included(key) => self.seek_le(key).map(|n| {
        let ent = VersionedEntryRef::from_node(n, &self.map.arena);
        self.last = Some(ent);
        ent
      }),
      Bound::Excluded(key) => self.seek_lt(key).map(|n| {
        let ent = VersionedEntryRef::from_node(n, &self.map.arena);
        self.last = Some(ent);
        ent
      }),
      Bound::Unbounded => self.last(),
    }
  }

  /// Moves the iterator to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  pub fn seek_lower_bound(&mut self, lower: Bound<&[u8]>) -> Option<VersionedEntryRef<'a, T>> {
    match lower {
      Bound::Included(key) => self.seek_ge(key).map(|n| {
        let ent = VersionedEntryRef::from_node(n, &self.map.arena);
        self.last = Some(ent);
        ent
      }),
      Bound::Excluded(key) => self.seek_gt(key).map(|n| {
        let ent = VersionedEntryRef::from_node(n, &self.map.arena);
        self.last = Some(ent);
        ent
      }),
      Bound::Unbounded => self.first(),
    }
  }

  /// Advances to the next position. Returns the key and value if the
  /// iterator is pointing at a valid entry, and `None` otherwise.
  fn next_in(&mut self) -> Option<VersionedEntryRef<T>> {
    loop {
      unsafe {
        self.nd = self.map.get_next(self.nd, 0);

        if self.nd.is_null() || self.nd.ptr == self.map.tail.ptr {
          return None;
        }

        let node = self.nd.as_ref();
        let (_, value, pointer) = node.get_value_and_trailer_with_pointer(&self.map.arena);
        if node.version() > self.version {
          continue;
        }

        if !self.all_versions && value.is_none() {
          continue;
        }

        let nk = node.get_key(&self.map.arena);

        if !self.all_versions {
          if let Some(last) = self.last {
            if self.map.cmp.compare(last.key, nk) == cmp::Ordering::Equal {
              continue;
            }
          }
        }

        if self.map.cmp.contains(
          self.range.start_bound().map(|b| b.borrow()),
          self.range.end_bound().map(|b| b.borrow()),
          nk,
        ) {
          let ent = VersionedEntryRef::from_node_with_pointer(self.nd, &self.map.arena, pointer);
          self.last = Some(ent);
          return Some(ent);
        }
      }
    }
  }

  /// Advances to the prev position. Returns the key and value if the
  /// iterator is pointing at a valid entry, and `None` otherwise.
  fn prev(&mut self) -> Option<VersionedEntryRef<T>> {
    loop {
      unsafe {
        self.nd = self.map.get_prev(self.nd, 0);

        if self.nd.is_null() || self.nd.ptr == self.map.head.ptr {
          return None;
        }

        let node = self.nd.as_ref();
        let (_, value, pointer) = node.get_value_and_trailer_with_pointer(&self.map.arena);
        if node.version() > self.version {
          continue;
        }

        if !self.all_versions && value.is_none() {
          continue;
        }

        let nk = node.get_key(&self.map.arena);

        if !self.all_versions {
          if let Some(last) = self.last {
            if self.map.cmp.compare(last.key, nk) == cmp::Ordering::Equal {
              continue;
            }
          }
        }

        if self.map.cmp.contains(
          self.range.start_bound().map(Borrow::borrow),
          self.range.end_bound().map(Borrow::borrow),
          nk,
        ) {
          let ent = VersionedEntryRef::from_node_with_pointer(self.nd, &self.map.arena, pointer);
          self.last = Some(ent);
          return Some(ent);
        }
      }
    }
  }

  /// Moves the iterator to the first entry whose key is greater than or
  /// equal to the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  fn seek_ge(&mut self, key: &[u8]) -> Option<NodePtr<T>> {
    self.nd = self.map.ge(self.version, key)?;
    if self.nd.is_null() || self.nd.ptr == self.map.tail.ptr {
      return None;
    }

    loop {
      unsafe {
        // Safety: the nd is valid, we already check this
        let node = self.nd.as_ref();
        // Safety: the node is allocated by the map's arena, so the key is valid
        let nk = node.get_key(&self.map.arena);

        if self.map.cmp.contains(
          self.range.start_bound().map(Borrow::borrow),
          self.range.end_bound().map(Borrow::borrow),
          nk,
        ) {
          return Some(self.nd);
        } else {
          let upper = self.range.end_bound();
          match upper {
            Bound::Included(upper) => {
              if self.map.cmp.compare(upper.borrow(), nk).is_lt() {
                return None;
              }
            }
            Bound::Excluded(upper) => {
              if self.map.cmp.compare(upper.borrow(), nk).is_le() {
                return None;
              }
            }
            Bound::Unbounded => {}
          }

          self.nd = self.map.get_next(self.nd, 0);
        }
      }
    }
  }

  /// Moves the iterator to the first entry whose key is greater than
  /// the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  fn seek_gt(&mut self, key: &[u8]) -> Option<NodePtr<T>> {
    self.nd = self.map.gt(self.version, key)?;

    if self.nd.is_null() || self.nd.ptr == self.map.tail.ptr {
      return None;
    }

    loop {
      unsafe {
        // Safety: the nd is valid, we already check this
        let node = self.nd.as_ref();
        // Safety: the node is allocated by the map's arena, so the key is valid
        let nk = node.get_key(&self.map.arena);

        if self.map.cmp.contains(
          self.range.start_bound().map(Borrow::borrow),
          self.range.end_bound().map(Borrow::borrow),
          nk,
        ) {
          return Some(self.nd);
        } else {
          let upper = self.range.end_bound();
          match upper {
            Bound::Included(upper) => {
              if self.map.cmp.compare(upper.borrow(), nk).is_lt() {
                return None;
              }
            }
            Bound::Excluded(upper) => {
              if self.map.cmp.compare(upper.borrow(), nk).is_le() {
                return None;
              }
            }
            Bound::Unbounded => {}
          }

          self.nd = self.map.get_next(self.nd, 0);
        }
      }
    }
  }

  /// Moves the iterator to the first entry whose key is less than or
  /// equal to the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  fn seek_le(&mut self, key: &[u8]) -> Option<NodePtr<T>> {
    self.nd = self.map.le(self.version, key)?;

    loop {
      unsafe {
        // Safety: the nd is valid, we already check this on line 75
        let node = self.nd.as_ref();

        // Safety: the node is allocated by the map's arena, so the key is valid
        let nk = node.get_key(&self.map.arena);

        if self.map.cmp.contains(
          self.range.start_bound().map(Borrow::borrow),
          self.range.end_bound().map(Borrow::borrow),
          nk,
        ) {
          return Some(self.nd);
        } else {
          let lower = self.range.start_bound();
          match lower {
            Bound::Included(lower) => {
              if self.map.cmp.compare(lower.borrow(), nk).is_gt() {
                return None;
              }
            }
            Bound::Excluded(lower) => {
              if self.map.cmp.compare(lower.borrow(), nk).is_ge() {
                return None;
              }
            }
            Bound::Unbounded => {}
          }

          self.nd = self.map.get_prev(self.nd, 0);
        }
      }
    }
  }

  /// Moves the iterator to the last entry whose key is less than the given
  /// key. Returns the key and value if the iterator is pointing at a valid entry,
  /// and `None` otherwise.
  fn seek_lt(&mut self, key: &[u8]) -> Option<NodePtr<T>> {
    // NB: the top-level AllVersionsIter has already adjusted key based on
    // the upper-bound.
    self.nd = self.map.lt(self.version, key)?;

    loop {
      unsafe {
        // Safety: the nd is valid, we already check this on line 75
        let node = self.nd.as_ref();
        // Safety: the node is allocated by the map's arena, so the key is valid
        let nk = node.get_key(&self.map.arena);

        if self.map.cmp.contains(
          self.range.start_bound().map(Borrow::borrow),
          self.range.end_bound().map(Borrow::borrow),
          nk,
        ) {
          return Some(self.nd);
        } else {
          let lower = self.range.start_bound();
          match lower {
            Bound::Included(lower) => {
              if self.map.cmp.compare(lower.borrow(), nk).is_gt() {
                return None;
              }
            }
            Bound::Excluded(lower) => {
              if self.map.cmp.compare(lower.borrow(), nk).is_ge() {
                return None;
              }
            }
            Bound::Unbounded => {}
          }

          self.nd = self.map.get_prev(self.nd, 0);
        }
      }
    }
  }

  /// Seeks position at the first entry in map. Returns the key and value
  /// if the iterator is pointing at a valid entry, and `None` otherwise.
  fn first(&mut self) -> Option<VersionedEntryRef<'a, T>> {
    self.nd = self.map.first_in(self.version)?;

    loop {
      if self.nd.is_null() || self.nd.ptr == self.map.tail.ptr {
        return None;
      }

      unsafe {
        let node = self.nd.as_ref();
        let nk = node.get_key(&self.map.arena);
        let (_, value, pointer) = node.get_value_and_trailer_with_pointer(&self.map.arena);

        if node.version() > self.version {
          self.nd = self.map.get_next(self.nd, 0);
          continue;
        }

        if !self.all_versions && value.is_none() {
          self.nd = self.map.get_next(self.nd, 0);
          continue;
        }

        if self.map.cmp.contains(
          self.range.start_bound().map(Borrow::borrow),
          self.range.end_bound().map(Borrow::borrow),
          nk,
        ) {
          let ent = VersionedEntryRef::from_node_with_pointer(self.nd, &self.map.arena, pointer);
          self.last = Some(ent);
          return Some(ent);
        }

        self.nd = self.map.get_next(self.nd, 0);
      }
    }
  }

  /// Seeks position at the last entry in the iterator. Returns the key and value if
  /// the iterator is pointing at a valid entry, and `None` otherwise.
  fn last(&mut self) -> Option<VersionedEntryRef<'a, T>> {
    self.nd = self.map.last_in(self.version)?;

    loop {
      unsafe {
        if self.nd.is_null() || self.nd.ptr == self.map.head.ptr {
          return None;
        }

        let node = self.nd.as_ref();
        let (_, value, pointer) = node.get_value_and_trailer_with_pointer(&self.map.arena);

        if node.version() > self.version {
          self.nd = self.map.get_prev(self.nd, 0);
          continue;
        }

        if !self.all_versions && value.is_none() {
          self.nd = self.map.get_prev(self.nd, 0);
          continue;
        }

        let nk = node.get_key(&self.map.arena);
        if self.map.cmp.contains(
          self.range.start_bound().map(Borrow::borrow),
          self.range.end_bound().map(Borrow::borrow),
          nk,
        ) {
          let ent = VersionedEntryRef::from_node_with_pointer(self.nd, &self.map.arena, pointer);
          return Some(ent);
        }

        self.nd = self.map.get_prev(self.nd, 0);
      }
    }
  }
}

impl<'a, Q, R, C, T> Iterator for AllVersionsIter<'a, C, T, Q, R>
where
  C: Comparator,
  T: Trailer,
  Q: ?Sized + Borrow<[u8]>,
  R: RangeBounds<Q>,
{
  type Item = VersionedEntryRef<'a, T>;

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
    self.seek_upper_bound(Bound::Unbounded).map(|e| {
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

impl<'a, Q, R, C, T> DoubleEndedIterator for AllVersionsIter<'a, C, T, Q, R>
where
  C: Comparator,
  T: Trailer,
  Q: ?Sized + Borrow<[u8]>,
  R: RangeBounds<Q>,
{
  fn next_back(&mut self) -> Option<Self::Item> {
    self.prev().map(|v| {
      // Safety: the EntryRef holds a reference to the map, so it is always valid.
      unsafe { core::mem::transmute(v) }
    })
  }
}
