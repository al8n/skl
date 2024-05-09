use core::cmp;

use super::{node::NodePtr, Comparator, SkipMap, Trailer};

/// An entry reference to the skipmap's entry.
#[derive(Debug)]
pub struct EntryRef<'a, T, C> {
  pub(super) map: &'a SkipMap<T, C>,
  pub(super) key: &'a [u8],
  pub(super) trailer: T,
  pub(super) value: &'a [u8],
}

impl<'a, T: Clone, C> Clone for EntryRef<'a, T, C> {
  fn clone(&self) -> Self {
    Self {
      map: self.map,
      key: self.key,
      trailer: self.trailer.clone(),
      value: self.value,
    }
  }
}

impl<'a, T: Copy, C> Copy for EntryRef<'a, T, C> {}

impl<'a, T, C> EntryRef<'a, T, C> {
  /// Returns the reference to the key
  #[inline]
  pub const fn key(&self) -> &[u8] {
    self.key
  }

  /// Returns the reference to the value
  #[inline]
  pub const fn value(&self) -> &[u8] {
    self.value
  }

  /// Returns the version of the entry
  #[inline]
  pub const fn trailer(&self) -> &T {
    &self.trailer
  }
}

impl<'a, T: Copy, C> EntryRef<'a, T, C> {
  pub(super) fn from_node(node: NodePtr<T>, map: &'a SkipMap<T, C>) -> EntryRef<'a, T, C> {
    unsafe {
      let node = node.as_ptr();
      EntryRef {
        key: node.get_key(&map.arena),
        trailer: node.trailer,
        value: node.get_value(&map.arena),
        map,
      }
    }
  }
}

impl<'a, T: Trailer, C: Comparator> PartialEq for EntryRef<'a, T, C> {
  fn eq(&self, other: &Self) -> bool {
    self
      .map
      .cmp
      .compare(self.key, other.key)
      .then_with(|| self.trailer.version().cmp(&other.trailer.version()))
      .is_eq()
  }
}

impl<'a, T: Trailer, C: Comparator> Eq for EntryRef<'a, T, C> {}

impl<'a, T: Trailer, C: Comparator> PartialOrd for EntryRef<'a, T, C> {
  fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
    Some(self.cmp(other))
  }
}

impl<'a, T: Trailer, C: Comparator> Ord for EntryRef<'a, T, C> {
  fn cmp(&self, other: &Self) -> cmp::Ordering {
    self.map.cmp.compare(self.key, other.key).then_with(|| {
      self
        .trailer
        .version()
        .cmp(&other.trailer.version())
        .reverse()
    })
  }
}
