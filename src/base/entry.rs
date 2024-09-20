use super::*;

/// A versioned entry reference of the skipmap.
///
/// Compared to the [`EntryRef`], this one's value can be `None` which means the entry is removed.
#[derive(Debug)]
pub struct VersionedEntryRef<'a, A: Allocator> {
  pub(super) arena: &'a A,
  pub(super) key: &'a [u8],
  pub(super) value_part_pointer: ValuePartPointer<A::Trailer>,
  pub(super) version: Version,
  pub(super) ptr: <A::Node as Node>::Pointer,
}

impl<A: Allocator> Clone for VersionedEntryRef<'_, A> {
  fn clone(&self) -> Self {
    *self
  }
}

impl<A: Allocator> Copy for VersionedEntryRef<'_, A> {}

impl<A> VersionedEntryRef<'_, A>
where
  A: Allocator,
  A::Node: WithTrailer,
{
  /// Returns the trailer of the entry
  #[inline]
  pub fn trailer(&self) -> &A::Trailer {
    unsafe {
      let node = self.ptr.as_ref(self.arena);
      let trailer = node.get_trailer_by_offset(self.arena, self.value_part_pointer.trailer_offset);
      trailer
    }
  }
}

impl<A: Allocator> VersionedEntryRef<'_, A> {
  /// Returns the reference to the key
  #[inline]
  pub const fn key(&self) -> &[u8] {
    self.key
  }

  /// Returns the reference to the value, `None` means the entry is removed.
  #[inline]
  pub fn value(&self) -> Option<&[u8]> {
    unsafe {
      let node = self.ptr.as_ref(self.arena);
      let value = node.get_value_by_value_offset(
        self.arena,
        self.value_part_pointer.value_offset,
        self.value_part_pointer.value_len,
      );
      value
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
  pub fn to_owned(self) -> VersionedEntry<A> {
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

impl<'a, A: Allocator> From<VersionedEntryRef<'a, A>> for VersionedEntry<A> {
  fn from(entry: VersionedEntryRef<'a, A>) -> Self {
    entry.to_owned()
  }
}

impl<'a, A: Allocator> VersionedEntryRef<'a, A> {
  #[inline]
  pub(super) fn from_node(
    node_ptr: <A::Node as Node>::Pointer,
    arena: &'a A,
  ) -> VersionedEntryRef<'a, A> {
    unsafe {
      let node = node_ptr.as_ref(arena);
      let vp = node.trailer_offset_and_value_size();
      VersionedEntryRef {
        key: node.get_key(arena),
        value_part_pointer: vp,
        arena,
        ptr: node_ptr,
        version: node.version(),
      }
    }
  }

  #[inline]
  pub(super) fn from_node_with_pointer(
    node_ptr: <A::Node as Node>::Pointer,
    arena: &'a A,
    pointer: ValuePartPointer<A::Trailer>,
  ) -> VersionedEntryRef<'a, A> {
    unsafe {
      let node = node_ptr.as_ref(arena);
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
pub struct VersionedEntry<A: Allocator> {
  pub(super) arena: A,
  pub(super) ptr: <A::Node as Node>::Pointer,
  pub(super) value_part_pointer: ValuePartPointer<A::Trailer>,
}

impl<A: Allocator> Clone for VersionedEntry<A> {
  fn clone(&self) -> Self {
    Self {
      arena: self.arena.clone(),
      ptr: self.ptr,
      value_part_pointer: self.value_part_pointer,
    }
  }
}

impl<'a, A: Allocator> From<&'a VersionedEntry<A>> for VersionedEntryRef<'a, A> {
  fn from(entry: &'a VersionedEntry<A>) -> VersionedEntryRef<'a, A> {
    entry.borrow()
  }
}

impl<A> VersionedEntry<A>
where
  A: Allocator,
  A::Node: WithTrailer,
{
  /// Returns the trailer of the entry
  #[inline]
  pub fn trailer(&self) -> &A::Trailer {
    unsafe {
      let node = self.ptr.as_ref(&self.arena);
      let trailer = node.get_trailer_by_offset(&self.arena, self.value_part_pointer.trailer_offset);
      trailer
    }
  }
}

impl<A: Allocator> VersionedEntry<A> {
  /// Returns the reference to the key
  #[inline]
  pub fn key(&self) -> &[u8] {
    unsafe {
      let node = self.ptr.as_ref(&self.arena);
      node.get_key(&self.arena)
    }
  }

  /// Returns the reference to the value, `None` means the entry is removed.
  #[inline]
  pub fn value(&self) -> Option<&[u8]> {
    unsafe {
      let node = self.ptr.as_ref(&self.arena);
      let value = node.get_value_by_value_offset(
        &self.arena,
        self.value_part_pointer.value_offset,
        self.value_part_pointer.value_len,
      );
      value
    }
  }

  /// Returns the borrowed entry reference
  #[inline]
  pub fn borrow(&self) -> VersionedEntryRef<'_, A> {
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
      let node = self.ptr.as_ref(&self.arena);
      node.version()
    }
  }
}

/// An owned entry of the skipmap.
///
/// Compared to the [`VersionedEntry`], this one's value cannot be `None`.
#[derive(Debug)]
pub struct Entry<A: Allocator>(VersionedEntry<A>);

impl<A: Allocator> Clone for Entry<A> {
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<'a, A: Allocator> From<&'a Entry<A>> for EntryRef<'a, A> {
  fn from(entry: &'a Entry<A>) -> Self {
    entry.borrow()
  }
}

impl<A> Entry<A>
where
  A: Allocator,
  A::Node: WithTrailer,
{
  /// Returns the trailer of the entry
  #[inline]
  pub fn trailer(&self) -> &A::Trailer {
    self.0.trailer()
  }
}

impl<A> Entry<A>
where
  A: Allocator,
  A::Node: WithVersion,
{
  /// Returns the version of the entry
  #[inline]
  pub fn version(&self) -> Version {
    self.0.version()
  }
}

impl<A: Allocator> Entry<A> {
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

  /// Returns the borrowed entry reference
  #[inline]
  pub fn borrow(&self) -> EntryRef<'_, A> {
    EntryRef(self.0.borrow())
  }
}

/// An entry reference to the skipmap's entry.
///
/// Compared to the [`VersionedEntryRef`], this one's value cannot be `None`.
#[derive(Debug)]
pub struct EntryRef<'a, A: Allocator>(pub(crate) VersionedEntryRef<'a, A>);

impl<A: Allocator> Clone for EntryRef<'_, A> {
  fn clone(&self) -> Self {
    *self
  }
}

impl<A: Allocator> Copy for EntryRef<'_, A> {}

impl<'a, A: Allocator> From<EntryRef<'a, A>> for Entry<A> {
  fn from(entry: EntryRef<'a, A>) -> Self {
    entry.to_owned()
  }
}

impl<A> EntryRef<'_, A>
where
  A: Allocator,
  A::Node: WithTrailer,
{
  /// Returns the trailer of the entry
  #[inline]
  pub fn trailer(&self) -> &A::Trailer {
    self.0.trailer()
  }
}

impl<A> EntryRef<'_, A>
where
  A: Allocator,
  A::Node: WithVersion,
{
  /// Returns the version of the entry
  #[inline]
  pub fn version(&self) -> Version {
    self.0.version()
  }
}

impl<A: Allocator> EntryRef<'_, A> {
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

  /// Returns the owned entry, feel free to clone the entry if needed, no allocation and no deep clone will be made.
  #[inline]
  pub fn to_owned(self) -> Entry<A> {
    Entry(self.0.to_owned())
  }
}
