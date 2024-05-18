use core::cmp;

use super::{node::NodePtr, Comparator, SkipMap, Trailer};

/// An optional entry reference to the skipmap's entry.
#[derive(Debug)]
pub struct OptionEntryRef<'a, T, C> {
  pub(super) map: &'a SkipMap<T, C>,
  pub(super) key: &'a [u8],
  pub(super) trailer: T,
  pub(super) value: Option<&'a [u8]>,
}

impl<'a, T: Clone, C> Clone for OptionEntryRef<'a, T, C> {
  fn clone(&self) -> Self {
    Self {
      map: self.map,
      key: self.key,
      trailer: self.trailer.clone(),
      value: self.value,
    }
  }
}

impl<'a, T: Copy, C> Copy for OptionEntryRef<'a, T, C> {}

impl<'a, T, C> OptionEntryRef<'a, T, C> {
  /// Returns the reference to the key
  #[inline]
  pub const fn key(&self) -> &[u8] {
    self.key
  }

  /// Returns the reference to the value, `None` means the entry is removed.
  #[inline]
  pub const fn value(&self) -> Option<&[u8]> {
    self.value
  }

  /// Returns the trailer of the entry
  #[inline]
  pub const fn trailer(&self) -> &T {
    &self.trailer
  }

  /// Returns if the entry is marked as removed
  #[inline]
  pub fn is_removed(&self) -> bool {
    self.value.is_none()
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

impl<'a, T: Copy, C> OptionEntryRef<'a, T, C> {
  pub(super) fn from_node(node: NodePtr<T>, map: &'a SkipMap<T, C>) -> OptionEntryRef<'a, T, C> {
    unsafe {
      let node = node.as_ptr();
      let (trailer, value) = node.get_value_and_trailer(&map.arena);
      OptionEntryRef {
        key: node.get_key(&map.arena),
        trailer,
        value,
        map,
      }
    }
  }
}

impl<'a, T: Trailer, C: Comparator> PartialEq for OptionEntryRef<'a, T, C> {
  fn eq(&self, other: &Self) -> bool {
    self
      .map
      .cmp
      .compare(self.key, other.key)
      .then_with(|| self.version().cmp(&other.version()))
      .is_eq()
  }
}

impl<'a, T: Trailer, C: Comparator> Eq for OptionEntryRef<'a, T, C> {}

impl<'a, T: Trailer, C: Comparator> PartialOrd for OptionEntryRef<'a, T, C> {
  fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
    Some(self.cmp(other))
  }
}

impl<'a, T: Trailer, C: Comparator> Ord for OptionEntryRef<'a, T, C> {
  fn cmp(&self, other: &Self) -> cmp::Ordering {
    self
      .map
      .cmp
      .compare(self.key, other.key)
      .then_with(|| self.version().cmp(&other.version()).reverse())
  }
}

/// An entry reference to the skipmap's entry.
#[derive(Debug)]
pub struct EntryRef<'a, T, C>(pub(crate) OptionEntryRef<'a, T, C>);

impl<'a, T: Clone, C> Clone for EntryRef<'a, T, C> {
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<'a, T: Copy, C> Copy for EntryRef<'a, T, C> {}

impl<'a, T, C> EntryRef<'a, T, C> {
  /// Returns the reference to the key
  #[inline]
  pub const fn key(&self) -> &[u8] {
    self.0.key()
  }

  /// Returns the reference to the value, `None` means the entry is removed.
  #[inline]
  pub const fn value(&self) -> &[u8] {
    match self.0.value() {
      Some(value) => value,
      None => panic!("EntryRef's value cannot be `None`"),
    }
  }

  /// Returns the trailer of the entry
  #[inline]
  pub const fn trailer(&self) -> &T {
    self.0.trailer()
  }

  /// Returns the version of the entry
  #[inline]
  pub fn version(&self) -> u64
  where
    T: Trailer,
  {
    self.0.version()
  }
}

impl<'a, T: Trailer, C: Comparator> PartialEq for EntryRef<'a, T, C> {
  fn eq(&self, other: &Self) -> bool {
    self.0.eq(&other.0)
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
    self.0.cmp(&other.0)
  }
}
