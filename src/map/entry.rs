use core::cmp;

use super::{node::NodePtr, Comparator, SkipMap, Trailer};

/// A versioned entry reference of the skipmap.
///
/// Compared to the [`EntryRef`], this one's value can be `None` which means the entry is removed.
#[derive(Debug)]
pub struct VersionedEntryRef<'a, T, C> {
  pub(super) map: &'a SkipMap<T, C>,
  pub(super) key: &'a [u8],
  pub(super) trailer: T,
  pub(super) value: Option<&'a [u8]>,
  pub(super) ptr: NodePtr<T>,
}

impl<'a, T: Clone, C> Clone for VersionedEntryRef<'a, T, C> {
  fn clone(&self) -> Self {
    Self {
      map: self.map,
      key: self.key,
      trailer: self.trailer.clone(),
      value: self.value,
      ptr: self.ptr,
    }
  }
}

impl<'a, T: Copy, C> Copy for VersionedEntryRef<'a, T, C> {}

impl<'a, T, C> VersionedEntryRef<'a, T, C> {
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
  pub const fn is_removed(&self) -> bool {
    self.value.is_none()
  }

  /// Returns the owned versioned entry,
  /// feel free to clone the entry if needed, no allocation and no deep clone will be made.
  #[inline]
  pub fn to_owned(&self) -> VersionedEntry<T, C>
  where
    T: Clone,
    C: Clone,
  {
    VersionedEntry {
      map: self.map.clone(),
      trailer: self.trailer.clone(),
      ptr: self.ptr,
    }
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

impl<'a, T: Clone, C: Clone> From<VersionedEntryRef<'a, T, C>> for VersionedEntry<T, C> {
  fn from(entry: VersionedEntryRef<'a, T, C>) -> Self {
    entry.to_owned()
  }
}

impl<'a, T: Copy, C> VersionedEntryRef<'a, T, C> {
  pub(super) fn from_node(
    node_ptr: NodePtr<T>,
    map: &'a SkipMap<T, C>,
  ) -> VersionedEntryRef<'a, T, C> {
    unsafe {
      let node = node_ptr.as_ptr();
      let (trailer, value) = node.get_value_and_trailer(&map.arena);
      VersionedEntryRef {
        key: node.get_key(&map.arena),
        trailer,
        value,
        map,
        ptr: node_ptr,
      }
    }
  }
}

impl<'a, T: Trailer, C: Comparator> PartialEq for VersionedEntryRef<'a, T, C> {
  fn eq(&self, other: &Self) -> bool {
    self
      .map
      .cmp
      .compare(self.key, other.key)
      .then_with(|| self.version().cmp(&other.version()))
      .is_eq()
  }
}

impl<'a, T: Trailer, C: Comparator> Eq for VersionedEntryRef<'a, T, C> {}

impl<'a, T: Trailer, C: Comparator> PartialOrd for VersionedEntryRef<'a, T, C> {
  fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
    Some(self.cmp(other))
  }
}

impl<'a, T: Trailer, C: Comparator> Ord for VersionedEntryRef<'a, T, C> {
  fn cmp(&self, other: &Self) -> cmp::Ordering {
    self
      .map
      .cmp
      .compare(self.key, other.key)
      .then_with(|| self.version().cmp(&other.version()).reverse())
  }
}

/// An owned versioned entry of the skipmap.
///
/// Compared to the [`Entry`], this one's value can be `None` which means the entry is removed.
#[derive(Debug)]
pub struct VersionedEntry<T, C> {
  pub(super) map: SkipMap<T, C>,
  pub(super) trailer: T,
  pub(super) ptr: NodePtr<T>,
}

impl<T: Clone, C: Clone> Clone for VersionedEntry<T, C> {
  fn clone(&self) -> Self {
    Self {
      map: self.map.clone(),
      trailer: self.trailer.clone(),
      ptr: self.ptr,
    }
  }
}

impl<'a, T: Clone, C> From<&'a VersionedEntry<T, C>> for VersionedEntryRef<'a, T, C> {
  fn from(entry: &'a VersionedEntry<T, C>) -> VersionedEntryRef<'a, T, C> {
    entry.borrow()
  }
}

impl<T, C> VersionedEntry<T, C> {
  /// Returns the reference to the key
  #[inline]
  pub const fn key(&self) -> &[u8] {
    unsafe {
      let node = self.ptr.as_ptr();
      node.get_key(&self.map.arena)
    }
  }

  /// Returns the reference to the value, `None` means the entry is removed.
  #[inline]
  pub fn value(&self) -> Option<&[u8]> {
    unsafe {
      let node = self.ptr.as_ptr();
      let value = node.get_value(&self.map.arena);
      value
    }
  }

  /// Returns the trailer of the entry
  #[inline]
  pub const fn trailer(&self) -> &T {
    &self.trailer
  }

  /// Returns the borrowed entry reference
  #[inline]
  pub fn borrow(&self) -> VersionedEntryRef<'_, T, C>
  where
    T: Clone,
  {
    VersionedEntryRef {
      map: &self.map,
      key: self.key(),
      trailer: self.trailer.clone(),
      value: self.value(),
      ptr: self.ptr,
    }
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

/// An owned entry of the skipmap.
///
/// Compared to the [`VersionedEntry`], this one's value cannot be `None`.
#[derive(Debug)]
pub struct Entry<T, C>(VersionedEntry<T, C>);

impl<T: Clone, C: Clone> Clone for Entry<T, C> {
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<'a, T: Clone, C> From<&'a Entry<T, C>> for EntryRef<'a, T, C> {
  fn from(entry: &'a Entry<T, C>) -> Self {
    entry.borrow()
  }
}

impl<T, C> Entry<T, C> {
  /// Returns the reference to the key
  #[inline]
  pub const fn key(&self) -> &[u8] {
    self.0.key()
  }

  /// Returns the reference to the value
  #[inline]
  pub fn value(&self) -> &[u8] {
    match self.0.value() {
      Some(value) => value,
      None => panic!("Entry's value cannot be `None`"),
    }
  }

  /// Returns the trailer of the entry
  #[inline]
  pub fn trailer(&self) -> &T {
    self.0.trailer()
  }

  /// Returns the borrowed entry reference
  #[inline]
  pub fn borrow(&self) -> EntryRef<'_, T, C>
  where
    T: Clone,
  {
    EntryRef(self.0.borrow())
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

/// An entry reference to the skipmap's entry.
///
/// Compared to the [`VersionedEntryRef`], this one's value cannot be `None`.
#[derive(Debug)]
pub struct EntryRef<'a, T, C>(pub(crate) VersionedEntryRef<'a, T, C>);

impl<'a, T: Clone, C> Clone for EntryRef<'a, T, C> {
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<'a, T: Copy, C> Copy for EntryRef<'a, T, C> {}

impl<'a, T: Clone, C: Clone> From<EntryRef<'a, T, C>> for Entry<T, C> {
  fn from(entry: EntryRef<'a, T, C>) -> Self {
    entry.to_owned()
  }
}

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

  /// Returns the owned entry, feel free to clone the entry if needed, no allocation and no deep clone will be made.
  #[inline]
  pub fn to_owned(&self) -> Entry<T, C>
  where
    T: Clone,
    C: Clone,
  {
    Entry(self.0.to_owned())
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
