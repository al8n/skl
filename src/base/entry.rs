use rarena_allocator::Arena;

use super::{NodePtr, Version};

#[derive(Copy, Clone, Debug)]
pub(super) struct ValuePartPointer {
  offset: u32,
  len: u32,
}

impl ValuePartPointer {
  #[inline]
  pub(super) const fn new(offset: u32, len: u32) -> Self {
    Self { offset, len }
  }
}

/// A versioned entry reference of the skipmap.
///
/// Compared to the [`EntryRef`], this one's value can be `None` which means the entry is removed.
#[derive(Debug)]
pub struct VersionedEntryRef<'a, T> {
  pub(super) arena: &'a Arena,
  pub(super) key: &'a [u8],
  pub(super) value_part_pointer: ValuePartPointer,
  pub(super) version: Version,
  pub(super) ptr: NodePtr<T>,
}

impl<'a, T> Clone for VersionedEntryRef<'a, T> {
  fn clone(&self) -> Self {
    *self
  }
}

impl<'a, T> Copy for VersionedEntryRef<'a, T> {}

impl<'a, T> VersionedEntryRef<'a, T> {
  /// Returns the reference to the key
  #[inline]
  pub const fn key(&self) -> &[u8] {
    self.key
  }

  /// Returns the reference to the value, `None` means the entry is removed.
  #[inline]
  pub fn value(&self) -> Option<&[u8]> {
    unsafe {
      let node = self.ptr.as_ref();
      let value = node.get_value_by_offset(
        self.arena,
        self.value_part_pointer.offset,
        self.value_part_pointer.len,
      );
      value
    }
  }

  /// Returns the trailer of the entry
  #[inline]
  pub fn trailer(&self) -> &T {
    unsafe {
      let node = self.ptr.as_ref();
      let trailer = node.get_trailer_by_offset(self.arena, self.value_part_pointer.offset);
      trailer
    }
  }

  /// Returns if the entry is marked as removed
  #[inline]
  pub fn is_removed(&self) -> bool {
    self.value().is_none()
  }

  /// Returns the owned versioned entry,
  /// feel free to clone the entry if needed, no allocation and no deep clone will be made.
  #[inline]
  pub fn to_owned(&self) -> VersionedEntry<T> {
    VersionedEntry {
      arena: self.arena.clone(),
      ptr: self.ptr,
      value_part_pointer: self.value_part_pointer,
    }
  }

  /// Returns the version of the entry
  #[inline]
  pub fn version(&self) -> Version {
    self.version
  }
}

impl<'a, T> From<VersionedEntryRef<'a, T>> for VersionedEntry<T> {
  fn from(entry: VersionedEntryRef<'a, T>) -> Self {
    entry.to_owned()
  }
}

impl<'a, T> VersionedEntryRef<'a, T> {
  #[inline]
  pub(super) fn from_node(node_ptr: NodePtr<T>, arena: &'a Arena) -> VersionedEntryRef<'a, T> {
    unsafe {
      let node = node_ptr.as_ref();
      let (offset, len) = node.trailer_offset_and_value_size();
      VersionedEntryRef {
        key: node.get_key(arena),
        value_part_pointer: ValuePartPointer::new(offset, len),
        arena,
        ptr: node_ptr,
        version: node.version(),
      }
    }
  }

  #[inline]
  pub(super) fn from_node_with_pointer(
    node_ptr: NodePtr<T>,
    arena: &'a Arena,
    pointer: ValuePartPointer,
  ) -> VersionedEntryRef<'a, T> {
    unsafe {
      let node = node_ptr.as_ref();
      VersionedEntryRef {
        key: node.get_key(arena),
        value_part_pointer: pointer,
        arena,
        ptr: node_ptr,
        version: node.version(),
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
  pub(super) ptr: NodePtr<T>,
  pub(super) value_part_pointer: ValuePartPointer,
}

impl<T> Clone for VersionedEntry<T> {
  fn clone(&self) -> Self {
    Self {
      arena: self.arena.clone(),
      ptr: self.ptr,
      value_part_pointer: self.value_part_pointer,
    }
  }
}

impl<'a, T> From<&'a VersionedEntry<T>> for VersionedEntryRef<'a, T> {
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
      let value = node.get_value_by_offset(
        &self.arena,
        self.value_part_pointer.offset,
        self.value_part_pointer.len,
      );
      value
    }
  }

  /// Returns the trailer of the entry
  #[inline]
  pub fn trailer(&self) -> &T {
    unsafe {
      let node = self.ptr.as_ref();
      let trailer = node.get_trailer_by_offset(&self.arena, self.value_part_pointer.offset);
      trailer
    }
  }

  /// Returns the borrowed entry reference
  #[inline]
  pub fn borrow(&self) -> VersionedEntryRef<'_, T> {
    VersionedEntryRef {
      arena: &self.arena,
      key: self.key(),
      value_part_pointer: self.value_part_pointer,
      ptr: self.ptr,
      version: self.version(),
    }
  }

  /// Returns the version of the entry
  #[inline]
  pub fn version(&self) -> Version {
    unsafe {
      let node = self.ptr.as_ref();
      node.version()
    }
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
  pub fn version(&self) -> Version {
    self.0.version()
  }
}

/// An entry reference to the skipmap's entry.
///
/// Compared to the [`VersionedEntryRef`], this one's value cannot be `None`.
#[derive(Debug)]
pub struct EntryRef<'a, T>(pub(crate) VersionedEntryRef<'a, T>);

impl<'a, T> Clone for EntryRef<'a, T> {
  fn clone(&self) -> Self {
    *self
  }
}

impl<'a, T> Copy for EntryRef<'a, T> {}

impl<'a, T> From<EntryRef<'a, T>> for Entry<T> {
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
  pub fn value(&self) -> &[u8] {
    match self.0.value() {
      Some(value) => value,
      None => panic!("EntryRef's value cannot be `None`"),
    }
  }

  /// Returns the trailer of the entry
  #[inline]
  pub fn trailer(&self) -> &T {
    self.0.trailer()
  }

  /// Returns the owned entry, feel free to clone the entry if needed, no allocation and no deep clone will be made.
  #[inline]
  pub fn to_owned(&self) -> Entry<T> {
    Entry(self.0.to_owned())
  }

  /// Returns the version of the entry
  #[inline]
  pub fn version(&self) -> Version {
    self.0.version()
  }
}
