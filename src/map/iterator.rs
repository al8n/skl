use core::cmp;

use crate::node::NodePtr;

use super::{Comparator, SkipMap};

/// An iterator over the skipmap. The current state of the iterator can be cloned by
/// simply value copying the struct.
pub struct MapIterator<'a, C = ()> {
  pub(super) map: &'a SkipMap<C>,
  pub(super) nd: NodePtr,
  pub(super) version: u64,
  pub(super) lower: Option<&'a [u8]>,
  pub(super) upper: Option<&'a [u8]>,
}

impl<'a, C> Clone for MapIterator<'a, C> {
  fn clone(&self) -> Self {
    *self
  }
}

impl<'a, C> Copy for MapIterator<'a, C> {}

impl<'a, C> MapIterator<'a, C>
where
  C: Comparator,
{
  /// Creates a new iterator over the skipmap.
  #[inline]
  pub const fn new(version: u64, map: &'a SkipMap<C>) -> Self {
    Self {
      map,
      nd: map.head,
      version,
      lower: None,
      upper: None,
    }
  }

  /// Creates a new iterator over the skipmap with the given lower and upper bounds.
  #[inline]
  pub fn bounded(
    map: &'a SkipMap<C>,
    version: u64,
    lower: &'a [u8],
    upper: &'a [u8],
  ) -> Option<Self> {
    match map.cmp.compare(lower, upper) {
      cmp::Ordering::Greater | cmp::Ordering::Equal => None,
      _ => Some(Self {
        map,
        nd: map.head,
        version,
        lower: Some(lower),
        upper: Some(upper),
      }),
    }
  }

  // /// Creates a new iterator over the skipmap with the given lower bound.
  // #[inline]
  // pub const fn bound_lower(map: &'a SkipMap<C>, lower: L) -> Self {
  //   Self {
  //     map,
  //     nd: map.head,
  //     lower: Some(lower),
  //     upper: None,
  //   }
  // }

  // /// Creates a new iterator over the skipmap with the given upper bound.
  // #[inline]
  // pub const fn bound_upper(map: &'a SkipMap<C>, upper: U) -> Self {
  //   Self {
  //     map,
  //     nd: map.head,
  //     lower: None,
  //     upper: Some(upper),
  //   }
  // }

  /// Seeks position at the first entry in map. Returns the key and value
  /// if the iterator is pointing at a valid entry, and `None` otherwise.
  pub fn first(&mut self) -> Option<(&[u8], &[u8])> {
    unsafe {
      match &self.lower {
        Some(lower) => {
          self.nd = self.map.ge_in(self.version, lower)?;
        }
        // No lower bound, so we can do quick path
        None => {
          self.nd = self.map.get_next(self.map.head, 0);
          if self.nd.ptr == self.map.tail.ptr {
            return None;
          }
        }
      }

      if let Some(upper) = self.upper {
        // Safety: the nd is valid, we already check this on line 113
        let node = self.nd.as_ptr();
        // Safety: the node is allocated by the map's arena, so the key is valid
        let nk = node.get_key(&self.map.arena);
        if let cmp::Ordering::Less | cmp::Ordering::Equal = self.map.cmp.compare(upper, nk) {
          self.nd = self.map.tail;
          return None;
        }
      }

      Some((self.key_unchecked(), self.value_unchecked()))
    }
  }

  /// Seeks position at the last entry in list. Returns the key and value if
  /// the iterator is pointing at a valid entry, and `None` otherwise. Note
  /// that Last only checks the lower bound. It is up to the caller to ensure that
  /// key is less than the upper bound (e.g. via a call to `seek_lt(upper)`).
  pub fn last(&mut self) -> Option<(&[u8], &[u8])> {
    unsafe {
      match &self.upper {
        Some(upper) => {
          self.nd = self.map.le_in(self.version, upper)?;
        }
        // No upper bound, so we can do quick path
        None => {
          self.nd = self.map.get_prev(self.map.tail, 0);
          if self.nd.ptr == self.map.head.ptr {
            return None;
          }
        }
      }

      if let Some(lower) = self.lower {
        // Safety: the nd is valid, we already check this on line 142
        let node = self.nd.as_ptr();
        // Safety: the node is allocated by the map's arena, so the key is valid
        let nk = node.get_key(&self.map.arena);
        if let cmp::Ordering::Greater = self.map.cmp.compare(lower, nk) {
          self.nd = self.map.head;
          return None;
        }
      }
      Some((self.key_unchecked(), self.value_unchecked()))
    }
  }

  /// Advances to the next position. Returns the key and value if the
  /// iterator is pointing at a valid entry, and `None` otherwise.
  #[allow(clippy::should_implement_trait)]
  pub fn next(&mut self) -> Option<(&[u8], &[u8])> {
    unsafe {
      self.nd = self.map.get_next(self.nd, 0);
      if self.nd.ptr == self.map.tail.ptr {
        return None;
      }

      if let Some(upper) = &self.upper {
        // Safety: the nd is valid, we already check this on line 168
        let node = self.nd.as_ptr();
        // Safety: the node is allocated by the map's arena, so the key is valid
        let nk = node.get_key(&self.map.arena);
        if let cmp::Ordering::Less | cmp::Ordering::Equal = self.map.cmp.compare(upper, nk) {
          self.nd = self.map.tail;
          return None;
        }
      }

      Some((self.key_unchecked(), self.value_unchecked()))
    }
  }

  /// Advances to the prev position. Returns the key and value if the
  /// iterator is pointing at a valid entry, and `None` otherwise.
  pub fn prev(&mut self) -> Option<(&[u8], &[u8])> {
    unsafe {
      self.nd = self.map.get_prev(self.nd, 0);
      if self.nd.ptr == self.map.head.ptr {
        return None;
      }

      if let Some(lower) = self.lower {
        // Safety: the nd is valid, we already check this on line 195
        let node = self.nd.as_ptr();
        // Safety: the node is allocated by the map's arena, so the key is valid
        let nk = node.get_key(&self.map.arena);
        if let cmp::Ordering::Greater = self.map.cmp.compare(lower, nk) {
          self.nd = self.map.head;
          return None;
        }
      }

      Some((self.key_unchecked(), self.value_unchecked()))
    }
  }

  /// Moves the iterator to the first entry whose key is greater than or
  /// equal to the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  pub fn seek_ge<'k: 'a, Q>(&'a mut self, key: &'k [u8]) -> Option<(&'a [u8], &'a [u8])> {
    self.nd = self.map.ge_in(self.version, key)?;

    unsafe {
      // Safety: the nd is valid, we already check this
      let node = self.nd.as_ptr();
      // Safety: the node is allocated by the map's arena, so the key is valid
      let nk = node.get_key(&self.map.arena);

      if let Some(upper) = self.upper {
        if let cmp::Ordering::Less = self.map.cmp.compare(upper, nk) {
          self.nd = self.map.tail;
          return None;
        }
      }

      if let Some(lower) = self.lower {
        if let cmp::Ordering::Greater = self.map.cmp.compare(lower, nk) {
          self.nd = self.map.head;
          return None;
        }
      }

      Some((self.key_unchecked(), self.value_unchecked()))
    }
  }

  /// Moves the iterator to the first entry whose key is greater than
  /// the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  pub fn seek_gt<'k: 'a>(&'a mut self, key: &'k [u8]) -> Option<(&'a [u8], &'a [u8])> {
    self.nd = self.map.gt_in(self.version, key)?;

    unsafe {
      // Safety: the nd is valid, we already check this
      let node = self.nd.as_ptr();
      // Safety: the node is allocated by the map's arena, so the key is valid
      let nk = node.get_key(&self.map.arena);

      if let Some(upper) = self.upper {
        if let cmp::Ordering::Less = self.map.cmp.compare(upper, nk) {
          self.nd = self.map.tail;
          return None;
        }
      }

      if let Some(lower) = self.lower {
        if let cmp::Ordering::Greater = self.map.cmp.compare(lower, nk) {
          self.nd = self.map.head;
          return None;
        }
      }

      Some((self.key_unchecked(), self.value_unchecked()))
    }
  }

  /// Moves the iterator to the first entry whose key is less than or
  /// equal to the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and `None` otherwise.
  pub fn seek_le<'k: 'a>(&'a mut self, key: &'k [u8]) -> Option<(&'a [u8], &'a [u8])> {
    // le_in has already checked the ptr is valid
    self.nd = self.map.le_in(self.version, key)?;

    unsafe {
      // Safety: the nd is valid, we already check this on line 75
      let node = self.nd.as_ptr();
      // Safety: the node is allocated by the map's arena, so the key is valid
      let nk = node.get_key(&self.map.arena);

      if let Some(lower) = self.lower {
        if let cmp::Ordering::Greater = self.map.cmp.compare(lower, nk) {
          self.nd = self.map.head;
          return None;
        }
      }

      if let Some(upper) = self.upper {
        if let cmp::Ordering::Less = self.map.cmp.compare(upper, nk) {
          self.nd = self.map.tail;
          return None;
        }
      }

      // Safety: the nd is valid, we already check this on line 115
      Some((self.key_unchecked(), self.value_unchecked()))
    }
  }

  /// Moves the iterator to the last entry whose key is less than the given
  /// key. Returns the key and value if the iterator is pointing at a valid entry,
  /// and `None` otherwise.
  pub fn seek_lt<'k: 'a>(&'a mut self, key: &'k [u8]) -> Option<(&'a [u8], &'a [u8])> {
    // NB: the top-level MapIterator has already adjusted key based on
    // the upper-bound.
    self.nd = self.map.lt_in(self.version, key)?;

    unsafe {
      // Safety: the nd is valid, we already check this on line 75
      let node = self.nd.as_ptr();
      // Safety: the node is allocated by the map's arena, so the key is valid
      let nk = node.get_key(&self.map.arena);

      if let Some(lower) = self.lower {
        if let cmp::Ordering::Greater | cmp::Ordering::Equal = self.map.cmp.compare(lower, nk) {
          self.nd = self.map.head;
          return None;
        }
      }

      if let Some(upper) = self.upper {
        if let cmp::Ordering::Equal | cmp::Ordering::Less = self.map.cmp.compare(upper, nk) {
          self.nd = self.map.tail;
          return None;
        }
      }

      // Safety: the nd is valid, we already check this on line 115
      Some((self.key_unchecked(), self.value_unchecked()))
    }
  }
}

impl<'a, C> MapIterator<'a, C>
where
  C: Comparator,
{
  /// Returns the key of the current entry without any checks.
  ///
  /// ## Safety
  /// - The current node must be valid
  unsafe fn key_unchecked(&self) -> &[u8] {
    let nd = self.nd.as_ptr();
    nd.get_key(&self.map.arena)
  }

  /// Returns the value of the current entry without any checks.
  ///
  /// ## Safety
  /// - The current node must be valid
  unsafe fn value_unchecked(&self) -> &[u8] {
    let nd = self.nd.as_ptr();
    nd.get_value(&self.map.arena)
  }
}
