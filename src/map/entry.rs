use rarena_allocator::Arena;

use super::{NodePtr, Trailer};

/// A versioned entry reference of the skipmap.
///
/// Compared to the [`EntryRef`], this one's value can be `None` which means the entry is removed.
#[derive(Debug)]
pub struct VersionedEntryRef<'a, T> {
  pub(super) arena: &'a Arena,
  pub(super) key: &'a [u8],
  pub(super) trailer: T,
  pub(super) value: Option<&'a [u8]>,
  pub(super) ptr: NodePtr<T>,
}

impl<'a, T: Clone> Clone for VersionedEntryRef<'a, T> {
  fn clone(&self) -> Self {
    Self {
      arena: self.arena,
      key: self.key,
      trailer: self.trailer.clone(),
      value: self.value,
      ptr: self.ptr,
    }
  }
}

impl<'a, T: Copy> Copy for VersionedEntryRef<'a, T> {}

impl<'a, T> VersionedEntryRef<'a, T> {
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
  pub fn to_owned(&self) -> VersionedEntry<T>
  where
    T: Clone,
  {
    VersionedEntry {
      arena: self.arena.clone(),
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

impl<'a, T: Clone> From<VersionedEntryRef<'a, T>> for VersionedEntry<T> {
  fn from(entry: VersionedEntryRef<'a, T>) -> Self {
    entry.to_owned()
  }
}

impl<'a, T: Copy> VersionedEntryRef<'a, T> {
  pub(super) fn from_node(node_ptr: NodePtr<T>, arena: &'a Arena) -> VersionedEntryRef<'a, T> {
    unsafe {
      let node = node_ptr.as_ref();
      let (trailer, value) = node.get_value_and_trailer(arena);
      VersionedEntryRef {
        key: node.get_key(arena),
        trailer,
        value,
        arena,
        ptr: node_ptr,
      }
    }
  }
}

/// An owned versioned entry of the skipmap.
///
/// Compared to the [`Entry`], this one's value can be `None` which means the entry is removed.
#[derive(Debug)]
pub struct VersionedEntry<T> {
  pub(super) arena: Arena,
  pub(super) trailer: T,
  pub(super) ptr: NodePtr<T>,
}

impl<T: Clone> Clone for VersionedEntry<T> {
  fn clone(&self) -> Self {
    Self {
      arena: self.arena.clone(),
      trailer: self.trailer.clone(),
      ptr: self.ptr,
    }
  }
}

impl<'a, T: Clone> From<&'a VersionedEntry<T>> for VersionedEntryRef<'a, T> {
  fn from(entry: &'a VersionedEntry<T>) -> VersionedEntryRef<'a, T> {
    entry.borrow()
  }
}

impl<T> VersionedEntry<T> {
  /// Returns the reference to the key
  #[inline]
  pub fn key(&self) -> &[u8] {
    unsafe {
      let node = self.ptr.as_ref();
      node.get_key(&self.arena)
    }
  }

  /// Returns the reference to the value, `None` means the entry is removed.
  #[inline]
  pub fn value(&self) -> Option<&[u8]> {
    unsafe {
      let node = self.ptr.as_ref();
      let value = node.get_value(&self.arena);
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
  pub fn borrow(&self) -> VersionedEntryRef<'_, T>
  where
    T: Clone,
  {
    VersionedEntryRef {
      arena: &self.arena,
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
pub struct Entry<T>(VersionedEntry<T>);

impl<T: Clone> Clone for Entry<T> {
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<'a, T: Clone> From<&'a Entry<T>> for EntryRef<'a, T> {
  fn from(entry: &'a Entry<T>) -> Self {
    entry.borrow()
  }
}

impl<T> Entry<T> {
  /// Returns the reference to the key
  #[inline]
  pub fn key(&self) -> &[u8] {
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
  pub fn borrow(&self) -> EntryRef<'_, T>
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
pub struct EntryRef<'a, T>(pub(crate) VersionedEntryRef<'a, T>);

impl<'a, T: Clone> Clone for EntryRef<'a, T> {
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<'a, T: Copy> Copy for EntryRef<'a, T> {}

impl<'a, T: Clone> From<EntryRef<'a, T>> for Entry<T> {
  fn from(entry: EntryRef<'a, T>) -> Self {
    entry.to_owned()
  }
}

impl<'a, T> EntryRef<'a, T> {
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
  pub fn to_owned(&self) -> Entry<T>
  where
    T: Clone,
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
