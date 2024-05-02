use core::ops::{Bound, RangeFull};

use super::*;

/// A range over the skipmap. The current state of the iterator can be cloned by
/// simply value copying the struct.
pub struct MapRange<'a, C = (), Q: ?Sized = &'static str, R = RangeFull>(MapIterator<'a, C, Q, R>);

impl<'a, C, Q, R> Clone for MapRange<'a, C, Q, R>
where
  R: Clone,
  Q: Clone,
{
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<'a, C, Q, R> Copy for MapRange<'a, C, Q, R>
where
  R: Copy,
  Q: Copy,
{
}

impl<'a, C, Q, R> core::ops::Deref for MapRange<'a, C, Q, R> {
  type Target = MapIterator<'a, C, Q, R>;

  fn deref(&self) -> &Self::Target {
    &self.0
  }
}

impl<'a, C, Q, R> core::ops::DerefMut for MapRange<'a, C, Q, R> {
  fn deref_mut(&mut self) -> &mut Self::Target {
    &mut self.0
  }
}

/// An iterator over the skipmap. The current state of the iterator can be cloned by
/// simply value copying the struct.
pub struct MapIterator<'a, C = (), Q: ?Sized = &'static [u8], R = core::ops::RangeFull> {
  pub(super) map: &'a SkipMap<C>,
  pub(super) nd: NodePtr,
  pub(super) version: u64,
  pub(super) range: R,
  // pub(super) lower: Bound<&'a [u8]>,
  // pub(super) upper: Bound<&'a [u8]>,

  // {lower|upper}_node are lazily populated with an arbitrary node that is
  // beyond the lower or upper bound respectively. Note the node is
  // "arbitrary" because it may not be the first node that exceeds the bound.
  // Concurrent insertions into the skiplist may introduce new nodes with keys
  // that exceed the bounds but are closer to the bounds than the current
  // values of [lower|upper]_node.
  //
  // Once populated, [lower|upper]_node may be used to detect when iteration
  // has reached a bound without performing a key comparison. This may be
  // beneficial when performing repeated `seek_ge`s with TrySeekUsingNext and an
  // upper bound set. Once the upper bound has been met, no additional key
  // comparisons are necessary.
  pub(super) lower_node: Option<NodePtr>,
  pub(super) upper_node: Option<NodePtr>,
  pub(super) _phantom: core::marker::PhantomData<Q>,
}

impl<'a, R: Clone, Q: Clone, C> Clone for MapIterator<'a, C, Q, R> {
  fn clone(&self) -> Self {
    Self {
      map: self.map,
      nd: self.nd,
      version: self.version,
      range: self.range.clone(),
      lower_node: self.lower_node,
      upper_node: self.upper_node,
      _phantom: core::marker::PhantomData,
    }
  }
}

impl<'a, R: Copy, Q: Copy, C> Copy for MapIterator<'a, C, Q, R> {}

impl<'a, C> MapIterator<'a, C>
where
  C: Comparator,
{
  #[inline]
  pub(super) const fn new(version: u64, map: &'a SkipMap<C>) -> Self {
    Self {
      map,
      nd: map.head,
      version,
      range: RangeFull,
      lower_node: None,
      upper_node: None,
      _phantom: core::marker::PhantomData,
    }
  }
}

impl<'a, Q, R, C> MapIterator<'a, C, Q, R>
where
  C: Comparator,
  &'a [u8]: PartialOrd<Q>,
  Q: ?Sized + PartialOrd<&'a [u8]>,
  R: RangeBounds<Q>,
{
  #[inline]
  pub(super) fn range(version: u64, map: &'a SkipMap<C>, r: R) -> MapRange<'a, C, Q, R> {
    MapRange(Self {
      map,
      nd: map.head,
      version,
      range: r,
      lower_node: None,
      upper_node: None,
      _phantom: core::marker::PhantomData,
    })
  }

  /// Seeks position at the first entry in map. Returns the key and value
  /// if the iterator is pointing at a valid entry, and `None` otherwise.
  pub fn first(&mut self) -> Option<EntryRef> {
    let mut cur = self.map.head;
    loop {
      unsafe {
        cur = self.map.get_next(cur, 0);
        self.nd = cur;
        if cur.is_null() || cur.ptr == self.map.tail.ptr {
          return None;
        }

        if let Some(ref upper) = self.upper_node {
          if cur.ptr == upper.ptr {
            return None;
          }
        }

        let node = cur.as_ptr();
        let nk = node.get_key(&self.map.arena);
        if self.map.cmp.contains(&self.range, nk) {
          self.lower_node.get_or_insert(cur);
          return Some(EntryRef {
            key: nk,
            version: node.version,
            value: node.get_value(&self.map.arena),
          });
        }
      }
    }
  }

  /// Seeks position at the last entry in the iterator. Returns the key and value if
  /// the iterator is pointing at a valid entry, and `None` otherwise.
  pub fn last(&mut self) -> Option<EntryRef> {
    let mut cur = self.map.tail;
    loop {
      unsafe {
        cur = self.map.get_prev(cur, 0);
        self.nd = cur;
        if cur.is_null() || cur.ptr == self.map.head.ptr {
          return None;
        }

        if let Some(ref lower) = self.lower_node {
          if cur.ptr == lower.ptr {
            return None;
          }
        }

        let node = cur.as_ptr();
        let nk = node.get_key(&self.map.arena);
        if self.map.cmp.contains(&self.range, nk) {
          self.upper_node.get_or_insert(cur);
          return Some(EntryRef {
            key: nk,
            version: node.version,
            value: node.get_value(&self.map.arena),
          });
        }
      }
    }
  }

  /// Advances to the next position. Returns the key and value if the
  /// iterator is pointing at a valid entry, and `None` otherwise.
  #[allow(clippy::should_implement_trait)]
  pub fn next(&mut self) -> Option<EntryRef> {
    unsafe {
      self.nd = self.map.get_next(self.nd, 0);

      if self.nd.is_null() || self.nd.ptr == self.map.tail.ptr {
        return None;
      }

      let node = self.nd.as_ptr();
      let nk = node.get_key(&self.map.arena);

      if self.map.cmp.contains(&self.range, nk) {
        return Some(EntryRef {
          key: nk,
          version: node.version,
          value: node.get_value(&self.map.arena),
        });
      }

      None
    }
  }

  /// Advances to the prev position. Returns the key and value if the
  /// iterator is pointing at a valid entry, and `None` otherwise.
  pub fn prev(&mut self) -> Option<EntryRef> {
    unsafe {
      self.nd = self.map.get_prev(self.nd, 0);

      if self.nd.is_null() || self.nd.ptr == self.map.head.ptr {
        return None;
      }

      let node = self.nd.as_ptr();
      let nk = node.get_key(&self.map.arena);

      if self.map.cmp.contains(&self.range, nk) {
        return Some(EntryRef {
          key: nk,
          version: node.version,
          value: node.get_value(&self.map.arena),
        });
      }

      None
    }
  }

  /// Moves the iterator to the first entry whose key is greater than or
  /// equal to the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  pub fn seek_ge(&mut self, key: &[u8]) -> Option<EntryRef<'_>> {
    self.nd = self.map.ge(self.version, key)?;

    loop {
      unsafe {
        // Safety: the nd is valid, we already check this
        let node = self.nd.as_ptr();
        // Safety: the node is allocated by the map's arena, so the key is valid
        let nk = node.get_key(&self.map.arena);

        if self.map.cmp.contains(&self.range, nk) {
          return Some(EntryRef {
            key: nk,
            version: node.version,
            value: node.get_value(&self.map.arena),
          });
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
  pub fn seek_gt(&mut self, key: &[u8]) -> Option<EntryRef<'_>> {
    self.nd = self.map.gt(self.version, key)?;

    loop {
      unsafe {
        // Safety: the nd is valid, we already check this
        let node = self.nd.as_ptr();
        // Safety: the node is allocated by the map's arena, so the key is valid
        let nk = node.get_key(&self.map.arena);

        if self.map.cmp.contains(&self.range, nk) {
          return Some(EntryRef {
            key: nk,
            version: node.version,
            value: node.get_value(&self.map.arena),
          });
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
  pub fn seek_le(&mut self, key: &[u8]) -> Option<EntryRef<'_>> {
    // le_in has already checked the ptr is valid
    self.nd = self.map.le(self.version, key)?;
    loop {
      unsafe {
        // Safety: the nd is valid, we already check this on line 75
        let node = self.nd.as_ptr();

        // Safety: the node is allocated by the map's arena, so the key is valid
        let nk = node.get_key(&self.map.arena);

        if self.map.cmp.contains(&self.range, nk) {
          return Some(EntryRef {
            key: nk,
            version: node.version,
            value: node.get_value(&self.map.arena),
          });
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
  pub fn seek_lt(&mut self, key: &[u8]) -> Option<EntryRef<'_>> {
    // NB: the top-level MapIterator has already adjusted key based on
    // the upper-bound.
    self.nd = self.map.lt(self.version, key)?;

    loop {
      unsafe {
        // Safety: the nd is valid, we already check this on line 75
        let node = self.nd.as_ptr();
        // Safety: the node is allocated by the map's arena, so the key is valid
        let nk = node.get_key(&self.map.arena);

        if self.map.cmp.contains(&self.range, nk) {
          return Some(EntryRef {
            key: nk,
            version: node.version,
            value: node.get_value(&self.map.arena),
          });
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
