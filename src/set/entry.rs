use core::cmp;

use super::{node::NodePtr, Comparator, SkipSet, Trailer};

/// An entry reference to the skipset's entry.
#[derive(Debug)]
pub struct EntryRef<'a, T, C> {
  pub(super) set: &'a SkipSet<T, C>,
  pub(super) key: &'a [u8],
  pub(super) trailer: T,
}

impl<'a, T: Clone, C> Clone for EntryRef<'a, T, C> {
  fn clone(&self) -> Self {
    Self {
      set: self.set,
      key: self.key,
      trailer: self.trailer.clone(),
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

  /// Returns the trailer of the entry
  #[inline]
  pub const fn trailer(&self) -> &T {
    &self.trailer
  }

  /// Returns the version of the entry
  #[inline]
  pub fn version(&self) -> u64
  where
    T: Trailer,
  {
    self.trailer.version()
  }
}

impl<'a, T: Copy, C> EntryRef<'a, T, C> {
  pub(super) fn from_node(node: NodePtr<T>, set: &'a SkipSet<T, C>) -> EntryRef<'a, T, C> {
    unsafe {
      let node = node.as_ptr();
      EntryRef {
        key: node.get_key(&set.arena),
        trailer: node.trailer,
        set,
      }
    }
  }
}

impl<'a, T: Trailer, C: Comparator> PartialEq for EntryRef<'a, T, C> {
  fn eq(&self, other: &Self) -> bool {
    self
      .set
      .cmp
      .compare(self.key, other.key)
      .then_with(|| self.version().cmp(&other.version()))
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
    self
      .set
      .cmp
      .compare(self.key, other.key)
      .then_with(|| self.version().cmp(&other.version()).reverse())
  }
}
