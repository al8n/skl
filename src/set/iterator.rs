use core::ops::RangeFull;

use super::*;

/// An iterator over the skipset. The current state of the iterator can be cloned by
/// simply value copying the struct.
pub struct SetIterator<'a, T, C, Q: ?Sized = &'static [u8], R = core::ops::RangeFull> {
  pub(super) set: &'a SkipSet<T, C>,
  pub(super) nd: NodePtr<T>,
  pub(super) version: u64,
  pub(super) range: R,
  pub(super) all_versions: bool,
  pub(super) last: Option<EntryRef<'a, T, C>>,
  pub(super) _phantom: core::marker::PhantomData<Q>,
}

impl<'a, R: Clone, Q: Clone, T: Clone, C> Clone for SetIterator<'a, T, C, Q, R> {
  fn clone(&self) -> Self {
    Self {
      set: self.set,
      nd: self.nd,
      version: self.version,
      range: self.range.clone(),
      last: self.last.clone(),
      all_versions: self.all_versions,
      _phantom: core::marker::PhantomData,
    }
  }
}

impl<'a, R: Copy, Q: Copy, T: Copy, C> Copy for SetIterator<'a, T, C, Q, R> {}

impl<'a, T, C> SetIterator<'a, T, C>
where
  C: Comparator,
{
  #[inline]
  pub(super) const fn new(version: u64, set: &'a SkipSet<T, C>, all_versions: bool) -> Self {
    Self {
      set,
      nd: set.head,
      version,
      range: RangeFull,
      last: None,
      all_versions,
      _phantom: core::marker::PhantomData,
    }
  }
}

impl<'a, Q, R, T, C> SetIterator<'a, T, C, Q, R>
where
  &'a [u8]: PartialOrd<Q>,
  Q: ?Sized + PartialOrd<&'a [u8]>,
{
  #[inline]
  pub(super) fn range(version: u64, set: &'a SkipSet<T, C>, r: R, all_versions: bool) -> Self {
    Self {
      set,
      nd: set.head,
      version,
      range: r,
      last: None,
      all_versions,
      _phantom: core::marker::PhantomData,
    }
  }
}

impl<'a, Q, R, T, C> SetIterator<'a, T, C, Q, R> {
  /// Returns the bounds of the iterator.
  #[inline]
  pub const fn bounds(&self) -> &R {
    &self.range
  }

  /// Returns the entry at the current position of the iterator.
  #[inline]
  pub const fn entry(&self) -> Option<&EntryRef<'a, T, C>> {
    self.last.as_ref()
  }
}

impl<'a, Q, R, T, C> SetIterator<'a, T, C, Q, R>
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
    match upper {
      Bound::Included(key) => self.seek_le(key).map(|n| {
        let ent = EntryRef::from_node(n, self.set);
        self.last = Some(ent);
        ent
      }),
      Bound::Excluded(key) => self.seek_lt(key).map(|n| {
        let ent = EntryRef::from_node(n, self.set);
        self.last = Some(ent);
        ent
      }),
      Bound::Unbounded => self.last(),
    }
  }

  /// Moves the iterator to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  pub fn seek_lower_bound(&mut self, lower: Bound<&[u8]>) -> Option<EntryRef<'a, T, C>> {
    match lower {
      Bound::Included(key) => self.seek_ge(key).map(|n| {
        let ent = EntryRef::from_node(n, self.set);
        self.last = Some(ent);
        ent
      }),
      Bound::Excluded(key) => self.seek_gt(key).map(|n| {
        let ent = EntryRef::from_node(n, self.set);
        self.last = Some(ent);
        ent
      }),
      Bound::Unbounded => self.first(),
    }
  }

  /// Advances to the next position. Returns the key and value if the
  /// iterator is pointing at a valid entry, and `None` otherwise.
  fn next_in(&mut self) -> Option<EntryRef<T, C>> {
    loop {
      unsafe {
        self.nd = self.set.get_next(self.nd, 0);

        if self.nd.is_null() || self.nd.ptr == self.set.tail.ptr {
          return None;
        }

        let node = self.nd.as_ptr();
        if node.trailer.version() > self.version {
          continue;
        }

        let nk = node.get_key(&self.set.arena);

        if !self.all_versions {
          if let Some(last) = self.last {
            if self.set.cmp.compare(last.key, nk) == cmp::Ordering::Equal {
              continue;
            }
          }
        }

        if self.set.cmp.contains(&self.range, nk) {
          let ent = EntryRef {
            set: self.set,
            key: nk,
            trailer: node.trailer,
          };
          self.last = Some(ent);
          return Some(ent);
        }
      }
    }
  }

  /// Advances to the prev position. Returns the key and value if the
  /// iterator is pointing at a valid entry, and `None` otherwise.
  fn prev(&mut self) -> Option<EntryRef<T, C>> {
    loop {
      unsafe {
        self.nd = self.set.get_prev(self.nd, 0);

        if self.nd.is_null() || self.nd.ptr == self.set.head.ptr {
          return None;
        }

        let node = self.nd.as_ptr();
        if node.trailer.version() > self.version {
          continue;
        }

        let nk = node.get_key(&self.set.arena);

        if !self.all_versions {
          if let Some(last) = self.last {
            if self.set.cmp.compare(last.key, nk) == cmp::Ordering::Equal {
              continue;
            }
          }
        }

        if self.set.cmp.contains(&self.range, nk) {
          let ent = EntryRef {
            set: self.set,
            key: nk,
            trailer: node.trailer,
          };
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
    self.nd = self.set.ge(self.version, key)?;
    if self.nd.is_null() || self.nd.ptr == self.set.tail.ptr {
      return None;
    }

    loop {
      unsafe {
        // Safety: the nd is valid, we already check this
        let node = self.nd.as_ptr();
        // Safety: the node is allocated by the set's arena, so the key is valid
        let nk = node.get_key(&self.set.arena);

        if self.set.cmp.contains(&self.range, nk) {
          return Some(self.nd);
        } else {
          let upper = self.range.end_bound();
          match upper {
            Bound::Included(upper) => {
              if upper.lt(&nk) {
                return None;
              }
            }
            Bound::Excluded(upper) => {
              if upper.le(&nk) {
                return None;
              }
            }
            Bound::Unbounded => {}
          }

          self.nd = self.set.get_next(self.nd, 0);
        }
      }
    }
  }

  /// Moves the iterator to the first entry whose key is greater than
  /// the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  fn seek_gt(&mut self, key: &[u8]) -> Option<NodePtr<T>> {
    self.nd = self.set.gt(self.version, key)?;

    if self.nd.is_null() || self.nd.ptr == self.set.tail.ptr {
      return None;
    }

    loop {
      unsafe {
        // Safety: the nd is valid, we already check this
        let node = self.nd.as_ptr();
        // Safety: the node is allocated by the set's arena, so the key is valid
        let nk = node.get_key(&self.set.arena);

        if self.set.cmp.contains(&self.range, nk) {
          return Some(self.nd);
        } else {
          let upper = self.range.end_bound();
          match upper {
            Bound::Included(upper) => {
              if upper.lt(&nk) {
                return None;
              }
            }
            Bound::Excluded(upper) => {
              if upper.le(&nk) {
                return None;
              }
            }
            Bound::Unbounded => {}
          }

          self.nd = self.set.get_next(self.nd, 0);
        }
      }
    }
  }

  /// Moves the iterator to the first entry whose key is less than or
  /// equal to the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  fn seek_le(&mut self, key: &[u8]) -> Option<NodePtr<T>> {
    self.nd = self.set.le(self.version, key)?;

    loop {
      unsafe {
        // Safety: the nd is valid, we already check this on line 75
        let node = self.nd.as_ptr();

        // Safety: the node is allocated by the set's arena, so the key is valid
        let nk = node.get_key(&self.set.arena);

        if self.set.cmp.contains(&self.range, nk) {
          return Some(self.nd);
        } else {
          let lower = self.range.start_bound();
          match lower {
            Bound::Included(lower) => {
              if lower.gt(&nk) {
                return None;
              }
            }
            Bound::Excluded(lower) => {
              if lower.ge(&nk) {
                return None;
              }
            }
            Bound::Unbounded => {}
          }

          self.nd = self.set.get_prev(self.nd, 0);
        }
      }
    }
  }

  /// Moves the iterator to the last entry whose key is less than the given
  /// key. Returns the key and value if the iterator is pointing at a valid entry,
  /// and `None` otherwise.
  fn seek_lt(&mut self, key: &[u8]) -> Option<NodePtr<T>> {
    // NB: the top-level SetIterator has already adjusted key based on
    // the upper-bound.
    self.nd = self.set.lt(self.version, key)?;

    loop {
      unsafe {
        // Safety: the nd is valid, we already check this on line 75
        let node = self.nd.as_ptr();
        // Safety: the node is allocated by the set's arena, so the key is valid
        let nk = node.get_key(&self.set.arena);

        if self.set.cmp.contains(&self.range, nk) {
          return Some(self.nd);
        } else {
          let lower = self.range.start_bound();
          match lower {
            Bound::Included(lower) => {
              if lower.gt(&nk) {
                return None;
              }
            }
            Bound::Excluded(lower) => {
              if lower.ge(&nk) {
                return None;
              }
            }
            Bound::Unbounded => {}
          }

          self.nd = self.set.get_prev(self.nd, 0);
        }
      }
    }
  }

  /// Seeks position at the first entry in set. Returns the key and value
  /// if the iterator is pointing at a valid entry, and `None` otherwise.
  fn first(&mut self) -> Option<EntryRef<'a, T, C>> {
    self.nd = self.set.first_in(self.version)?;

    loop {
      if self.nd.is_null() || self.nd.ptr == self.set.tail.ptr {
        return None;
      }

      unsafe {
        let node = self.nd.as_ptr();
        let nk = node.get_key(&self.set.arena);

        if node.trailer.version() > self.version {
          self.nd = self.set.get_next(self.nd, 0);
          continue;
        }

        if self.set.cmp.contains(&self.range, nk) {
          let ent = EntryRef {
            set: self.set,
            key: nk,
            trailer: node.trailer,
          };
          self.last = Some(ent);
          return Some(ent);
        }

        self.nd = self.set.get_next(self.nd, 0);
      }
    }
  }

  /// Seeks position at the last entry in the iterator. Returns the key and value if
  /// the iterator is pointing at a valid entry, and `None` otherwise.
  fn last(&mut self) -> Option<EntryRef<'a, T, C>> {
    self.nd = self.set.last_in(self.version)?;

    loop {
      unsafe {
        if self.nd.is_null() || self.nd.ptr == self.set.head.ptr {
          return None;
        }

        let node = self.nd.as_ptr();
        if node.trailer.version() > self.version {
          self.nd = self.set.get_prev(self.nd, 0);
          continue;
        }

        let nk = node.get_key(&self.set.arena);
        if self.set.cmp.contains(&self.range, nk) {
          let ent = EntryRef {
            set: self.set,
            key: nk,
            trailer: node.trailer,
          };
          return Some(ent);
        }

        self.nd = self.set.get_prev(self.nd, 0);
      }
    }
  }
}

impl<'a, Q, R, T, C> Iterator for SetIterator<'a, T, C, Q, R>
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
    self.next_in().map(|v| {
      // Safety: the EntryRef holds a reference to the set, so it is always valid.
      unsafe { core::mem::transmute(v) }
    })
  }

  #[inline]
  fn last(mut self) -> Option<Self::Item>
  where
    Self: Sized,
  {
    self.seek_upper_bound(Bound::Unbounded).map(|e| {
      // Safety: the EntryRef holds a reference to the set, so it is always valid.
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
      // Safety: the EntryRef holds a reference to the set, so it is always valid.
      unsafe { core::mem::transmute(e) }
    })
  }
}

impl<'a, Q, R, T, C> DoubleEndedIterator for SetIterator<'a, T, C, Q, R>
where
  C: Comparator,
  T: Trailer,
  &'a [u8]: PartialOrd<Q>,
  Q: ?Sized + PartialOrd<&'a [u8]>,
  R: RangeBounds<Q>,
{
  fn next_back(&mut self) -> Option<Self::Item> {
    self.prev().map(|v| {
      // Safety: the EntryRef holds a reference to the set, so it is always valid.
      unsafe { core::mem::transmute(v) }
    })
  }
}
