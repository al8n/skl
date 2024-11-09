use crate::{
  allocator::{Allocator, Node, NodePointer, WithVersion},
  dynamic::list::SkipList,
  types::internal::ValuePointer,
  Version,
};
use dbutils::equivalentor::Comparator;

/// A versioned entry reference of the skipmap.
///
/// Compared to the [`EntryRef`], this one's value can be `None` which means the entry is removed.
pub struct VersionedEntryRef<'a, A, C>
where
  A: Allocator,
{
  pub(super) list: &'a SkipList<A, C>,
  pub(super) key: &'a [u8],
  pub(super) value: Option<&'a [u8]>,
  pub(super) version: Version,
  pub(super) query_version: Version,
  pub(super) ptr: <A::Node as Node>::Pointer,
}

impl<A, C> core::fmt::Debug for VersionedEntryRef<'_, A, C>
where
  A: Allocator,
{
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("VersionedEntryRef")
      .field("key", &self.key())
      .field("value", &self.value())
      .field("version", &self.version)
      .finish()
  }
}

impl<A, C> Clone for VersionedEntryRef<'_, A, C>
where
  A: Allocator,
{
  fn clone(&self) -> Self {
    *self
  }
}

impl<A, C> Copy for VersionedEntryRef<'_, A, C> where A: Allocator {}

impl<'a, A, C> VersionedEntryRef<'a, A, C>
where
  A: Allocator,
{
  /// Returns the reference to the key
  #[inline]
  pub const fn key(&self) -> &'a [u8] {
    self.key
  }

  /// Returns the reference to the value, `None` means the entry is removed.
  #[inline]
  pub const fn value(&self) -> Option<&'a [u8]> {
    self.value
  }

  /// Returns if the entry is marked as removed
  #[inline]
  pub fn is_removed(&self) -> bool {
    self.value().is_none()
  }
}

impl<A, C> VersionedEntryRef<'_, A, C>
where
  C: Comparator,
  A: Allocator,
{
  /// Returns the next entry in the map.
  #[inline]
  pub fn next(&self) -> Option<Self> {
    self.next_in(true)
  }

  /// Returns the previous entry in the map.
  #[inline]
  pub fn prev(&self) -> Option<Self> {
    self.prev_in(true)
  }

  fn next_in(&self, all_versions: bool) -> Option<Self> {
    let mut nd = self.ptr;
    if all_versions {
      unsafe {
        nd = self.list.get_next(nd, 0);
        self
          .list
          .move_to_next(&mut nd, self.query_version, |_| true)
      }
    } else {
      unsafe {
        nd = self.list.get_next(nd, 0);
        self
          .list
          .move_to_next_maximum_version(&mut nd, self.query_version, |_| true)
      }
    }
  }

  fn prev_in(&self, all_versions: bool) -> Option<Self> {
    let mut nd = self.ptr;
    if all_versions {
      unsafe {
        nd = self.list.get_prev(nd, 0);
        self
          .list
          .move_to_prev(&mut nd, self.query_version, |_| true)
      }
    } else {
      unsafe {
        nd = self.list.get_prev(nd, 0);
        self
          .list
          .move_to_prev_maximum_version(&mut nd, self.query_version, |_| true)
      }
    }
  }
}

impl<A, C> VersionedEntryRef<'_, A, C>
where
  A: Allocator,
  A::Node: WithVersion,
{
  /// Returns the version of the entry
  #[inline]
  pub const fn version(&self) -> Version {
    self.version
  }
}

impl<'a, A, C> VersionedEntryRef<'a, A, C>
where
  A: Allocator,
{
  #[inline]
  pub(crate) fn from_node(
    query_version: Version,
    node: <A::Node as Node>::Pointer,
    list: &'a SkipList<A, C>,
    key: Option<&'a [u8]>,
  ) -> Self {
    unsafe {
      let (value, _) = node.get_value_with_pointer(&list.arena);

      let key = match key {
        Some(key) => key,
        None => node.get_key(&list.arena),
      };

      Self {
        list,
        key,
        value,
        version: node.version(),
        query_version,
        ptr: node,
      }
    }
  }

  #[inline]
  pub(crate) fn from_node_with_pointer(
    query_version: Version,
    node: <A::Node as Node>::Pointer,
    list: &'a SkipList<A, C>,
    pointer: ValuePointer,
    key: Option<&'a [u8]>,
  ) -> Self {
    unsafe {
      let value =
        node.get_value_by_value_offset(&list.arena, pointer.value_offset, pointer.value_len);

      let key = match key {
        Some(key) => key,
        None => node.get_key(&list.arena),
      };

      Self {
        list,
        key,
        value,
        version: node.version(),
        query_version,
        ptr: node,
      }
    }
  }
}

/// An entry reference to the skipmap's entry.
///
/// Compared to the [`VersionedEntryRef`], this one's value cannot be `None`.
pub struct EntryRef<'a, A, C>(pub(crate) VersionedEntryRef<'a, A, C>)
where
  A: Allocator;

impl<A, C> core::fmt::Debug for EntryRef<'_, A, C>
where
  A: Allocator,
{
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("EntryRef")
      .field("key", &self.key())
      .field("value", &self.value())
      .finish()
  }
}

impl<A, C> Clone for EntryRef<'_, A, C>
where
  A: Allocator,
{
  #[inline]
  fn clone(&self) -> Self {
    *self
  }
}

impl<A, C> Copy for EntryRef<'_, A, C> where A: Allocator {}

impl<A, C> EntryRef<'_, A, C>
where
  C: Comparator,
  A: Allocator,
{
  /// Returns the next entry in the map.
  #[inline]
  pub fn next(&self) -> Option<Self> {
    self.0.next_in(false).map(Self)
  }

  /// Returns the previous entry in the map.
  #[inline]
  pub fn prev(&self) -> Option<Self> {
    self.0.prev_in(false).map(Self)
  }
}

impl<A, C> EntryRef<'_, A, C>
where
  A: Allocator,
  A::Node: WithVersion,
{
  /// Returns the version of the entry
  #[inline]
  pub const fn version(&self) -> Version {
    self.0.version()
  }
}

impl<'a, A, C> EntryRef<'a, A, C>
where
  A: Allocator,
{
  /// Returns the reference to the key
  #[inline]
  pub fn key(&self) -> &'a [u8] {
    self.0.key()
  }

  /// Returns the reference to the value
  #[inline]
  pub fn value(&self) -> &'a [u8] {
    self.0.value().expect("EntryRef's value cannot be `None`")
  }
}
