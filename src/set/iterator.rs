use core::ops::RangeFull;

use super::*;

/// A range over the skipmap. The current state of the iterator can be cloned by
/// simply value copying the struct.
pub struct SetRange<'a, C = Ascend, Q: ?Sized = &'static str, R = RangeFull>(
  SetIterator<'a, C, Q, R>,
);

impl<'a, C, Q, R> Clone for SetRange<'a, C, Q, R>
where
  R: Clone,
  Q: Clone,
{
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<'a, C, Q, R> Copy for SetRange<'a, C, Q, R>
where
  R: Copy,
  Q: Copy,
{
}

impl<'a, C, Q, R> core::ops::Deref for SetRange<'a, C, Q, R> {
  type Target = SetIterator<'a, C, Q, R>;

  fn deref(&self) -> &Self::Target {
    &self.0
  }
}

impl<'a, C, Q, R> core::ops::DerefMut for SetRange<'a, C, Q, R> {
  fn deref_mut(&mut self) -> &mut Self::Target {
    &mut self.0
  }
}

/// An iterator over the skipmap. The current state of the iterator can be cloned by
/// simply value copying the struct.
pub struct SetIterator<'a, C = Ascend, Q: ?Sized = &'static [u8], R = core::ops::RangeFull> {
  pub(super) map: &'a SkipSet<C>,
  pub(super) nd: NodePtr,
  pub(super) version: u64,
  pub(super) range: R,
  pub(super) _phantom: core::marker::PhantomData<Q>,
}

impl<'a, R: Clone, Q: Clone, C> Clone for SetIterator<'a, C, Q, R> {
  fn clone(&self) -> Self {
    Self {
      map: self.map,
      nd: self.nd,
      version: self.version,
      range: self.range.clone(),
      _phantom: core::marker::PhantomData,
    }
  }
}

impl<'a, R: Copy, Q: Copy, C> Copy for SetIterator<'a, C, Q, R> {}

impl<'a, C> SetIterator<'a, C>
where
  C: Comparator,
{
  #[inline]
  pub(super) const fn new(version: u64, map: &'a SkipSet<C>) -> Self {
    Self {
      map,
      nd: map.head,
      version,
      range: RangeFull,
      _phantom: core::marker::PhantomData,
    }
  }
}

impl<'a, Q, R, C> SetIterator<'a, C, Q, R>
where
  C: Comparator,
  &'a [u8]: PartialOrd<Q>,
  Q: ?Sized + PartialOrd<&'a [u8]>,
  R: RangeBounds<Q>,
{
  #[inline]
  pub(super) fn range(version: u64, map: &'a SkipSet<C>, r: R) -> SetRange<'a, C, Q, R> {
    SetRange(Self {
      map,
      nd: map.head,
      version,
      range: r,
      _phantom: core::marker::PhantomData,
    })
  }

  /// Seeks position at the first entry in map. Returns the key and value
  /// if the iterator is pointing at a valid entry, and `None` otherwise.
  pub fn first(&mut self) -> Option<EntryRef> {
    self.nd = self.map.first_in(self.version)?;

    loop {
      if self.nd.is_null() || self.nd.ptr == self.map.tail.ptr {
        return None;
      }

      unsafe {
        let node = self.nd.as_ptr();
        let nk = node.get_key(&self.map.arena);

        if node.version > self.version {
          self.nd = self.map.get_next(self.nd, 0);
          continue;
        }

        if self.map.cmp.contains(&self.range, nk) {
          return Some(EntryRef {
            key: nk,
            version: node.version,
          });
        }

        self.nd = self.map.get_next(self.nd, 0);
      }
    }
  }

  /// Seeks position at the last entry in the iterator. Returns the key and value if
  /// the iterator is pointing at a valid entry, and `None` otherwise.
  pub fn last(&mut self) -> Option<EntryRef> {
    self.nd = self.map.last_in(self.version)?;

    loop {
      unsafe {
        if self.nd.is_null() || self.nd.ptr == self.map.head.ptr {
          return None;
        }

        let node = self.nd.as_ptr();
        if node.version > self.version {
          self.nd = self.map.get_prev(self.nd, 0);
          continue;
        }

        let nk = node.get_key(&self.map.arena);
        if self.map.cmp.contains(&self.range, nk) {
          return Some(EntryRef {
            key: nk,
            version: node.version,
          });
        }

        self.nd = self.map.get_prev(self.nd, 0);
      }
    }
  }

  /// Advances to the next position. Returns the key and value if the
  /// iterator is pointing at a valid entry, and `None` otherwise.
  #[allow(clippy::should_implement_trait)]
  pub fn next(&mut self) -> Option<EntryRef> {
    loop {
      unsafe {
        self.nd = self.map.get_next(self.nd, 0);

        if self.nd.is_null() || self.nd.ptr == self.map.tail.ptr {
          return None;
        }

        let node = self.nd.as_ptr();
        if node.version > self.version {
          continue;
        }

        let nk = node.get_key(&self.map.arena);

        if self.map.cmp.contains(&self.range, nk) {
          return Some(EntryRef {
            key: nk,
            version: node.version,
          });
        }
      }
    }
  }

  /// Advances to the prev position. Returns the key and value if the
  /// iterator is pointing at a valid entry, and `None` otherwise.
  pub fn prev(&mut self) -> Option<EntryRef> {
    loop {
      unsafe {
        self.nd = self.map.get_prev(self.nd, 0);

        if self.nd.is_null() || self.nd.ptr == self.map.head.ptr {
          return None;
        }

        let node = self.nd.as_ptr();
        if node.version > self.version {
          continue;
        }

        let nk = node.get_key(&self.map.arena);

        if self.map.cmp.contains(&self.range, nk) {
          return Some(EntryRef {
            key: nk,
            version: node.version,
          });
        }
      }
    }
  }

  /// Moves the iterator to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  pub fn seek_upper_bound(&mut self, upper: Bound<&[u8]>) -> Option<EntryRef<'_>> {
    match upper {
      Bound::Included(key) => self
        .seek_le(key)
        .map(|n| EntryRef::from_node(n, &self.map.arena)),
      Bound::Excluded(key) => self
        .seek_lt(key)
        .map(|n| EntryRef::from_node(n, &self.map.arena)),
      Bound::Unbounded => self.last(),
    }
  }

  /// Moves the iterator to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  pub fn seek_lower_bound(&mut self, lower: Bound<&[u8]>) -> Option<EntryRef<'_>> {
    match lower {
      Bound::Included(key) => self
        .seek_ge(key)
        .map(|n| EntryRef::from_node(n, &self.map.arena)),
      Bound::Excluded(key) => self
        .seek_gt(key)
        .map(|n| EntryRef::from_node(n, &self.map.arena)),
      Bound::Unbounded => self.first(),
    }
  }

  /// Moves the iterator to the first entry whose key is greater than or
  /// equal to the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  fn seek_ge(&mut self, key: &[u8]) -> Option<NodePtr> {
    self.nd = self.map.ge(self.version, key)?;
    if self.nd.is_null() || self.nd.ptr == self.map.tail.ptr {
      return None;
    }

    loop {
      unsafe {
        // Safety: the nd is valid, we already check this
        let node = self.nd.as_ptr();
        // Safety: the node is allocated by the map's arena, so the key is valid
        let nk = node.get_key(&self.map.arena);

        if self.map.cmp.contains(&self.range, nk) {
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
          self.next();
        }
      }
    }
  }

  /// Moves the iterator to the first entry whose key is greater than
  /// the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  fn seek_gt(&mut self, key: &[u8]) -> Option<NodePtr> {
    self.nd = self.map.gt(self.version, key)?;

    if self.nd.is_null() || self.nd.ptr == self.map.tail.ptr {
      return None;
    }

    loop {
      unsafe {
        // Safety: the nd is valid, we already check this
        let node = self.nd.as_ptr();
        // Safety: the node is allocated by the map's arena, so the key is valid
        let nk = node.get_key(&self.map.arena);

        if self.map.cmp.contains(&self.range, nk) {
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
          self.next();
        }
      }
    }
  }

  /// Moves the iterator to the first entry whose key is less than or
  /// equal to the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  fn seek_le(&mut self, key: &[u8]) -> Option<NodePtr> {
    self.nd = self.map.le(self.version, key)?;

    loop {
      unsafe {
        // Safety: the nd is valid, we already check this on line 75
        let node = self.nd.as_ptr();

        // Safety: the node is allocated by the map's arena, so the key is valid
        let nk = node.get_key(&self.map.arena);

        if self.map.cmp.contains(&self.range, nk) {
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

          self.prev();
        }
      }
    }
  }

  /// Moves the iterator to the last entry whose key is less than the given
  /// key. Returns the key and value if the iterator is pointing at a valid entry,
  /// and `None` otherwise.
  fn seek_lt(&mut self, key: &[u8]) -> Option<NodePtr> {
    // NB: the top-level SetIterator has already adjusted key based on
    // the upper-bound.
    self.nd = self.map.lt(self.version, key)?;

    loop {
      unsafe {
        // Safety: the nd is valid, we already check this on line 75
        let node = self.nd.as_ptr();
        // Safety: the node is allocated by the map's arena, so the key is valid
        let nk = node.get_key(&self.map.arena);

        if self.map.cmp.contains(&self.range, nk) {
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

          self.prev();
        }
      }
    }
  }
}
