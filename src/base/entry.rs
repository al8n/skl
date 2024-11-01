use dbutils::types::{KeyRef, LazyRef, Type};

use crate::{
  allocator::{Allocator, Node, NodePointer, ValuePartPointer, WithVersion},
  base::SkipList,
  Version,
};

/// A versioned entry reference of the skipmap.
///
/// Compared to the [`EntryRef`], this one's value can be `None` which means the entry is removed.
pub struct VersionedEntryRef<'a, K, V, A>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  A: Allocator,
{
  pub(super) list: &'a SkipList<K, V, A>,
  pub(super) key: LazyRef<'a, K>,
  pub(super) value: Option<LazyRef<'a, V>>,
  pub(super) value_part_pointer: ValuePartPointer,
  pub(super) version: Version,
  pub(super) query_version: Version,
  pub(super) ptr: <A::Node as Node>::Pointer,
}

impl<K, V, A> core::fmt::Debug for VersionedEntryRef<'_, K, V, A>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
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

impl<'a, K, V, A: Allocator> Clone for VersionedEntryRef<'a, K, V, A>
where
  K: ?Sized + Type,
  K::Ref<'a>: Clone,
  V: ?Sized + Type,
  V::Ref<'a>: Clone,
  A: Allocator,
{
  fn clone(&self) -> Self {
    Self {
      list: self.list,
      key: self.key.clone(),
      value: self.value.clone(),
      value_part_pointer: self.value_part_pointer,
      version: self.version,
      query_version: self.query_version,
      ptr: self.ptr,
    }
  }
}

impl<'a, K, V, A: Allocator> VersionedEntryRef<'a, K, V, A>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  A: Allocator,
{
  /// Returns the reference to the key
  #[inline]
  pub fn key(&self) -> &K::Ref<'a> {
    self.key.get()
  }

  /// Returns the key in raw bytes
  #[inline]
  pub fn raw_key(&self) -> &'a [u8] {
    self.key.raw().expect("raw key must be available")
  }

  /// Returns the reference to the value, `None` means the entry is removed.
  #[inline]
  pub fn value(&self) -> Option<&V::Ref<'a>> {
    self.value.as_deref()
  }

  /// Returns the value in raw bytes
  #[inline]
  pub fn raw_value(&self) -> Option<&'a [u8]> {
    self
      .value
      .as_ref()
      .map(|value| value.raw().expect("raw value must be available"))
  }

  /// Returns if the entry is marked as removed
  #[inline]
  pub fn is_removed(&self) -> bool {
    self.value().is_none()
  }
}

impl<'a, K, V, A: Allocator> VersionedEntryRef<'a, K, V, A>
where
  K: ?Sized + Type,
  K::Ref<'a>: KeyRef<'a, K>,
  V: ?Sized + Type,
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

impl<K, V, A> VersionedEntryRef<'_, K, V, A>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  A: Allocator,
  A::Node: WithVersion,
{
  /// Returns the version of the entry
  #[inline]
  pub fn version(&self) -> Version {
    self.version
  }
}

impl<'a, K, V, A> VersionedEntryRef<'a, K, V, A>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  A: Allocator,
{
  #[inline]
  pub(crate) fn from_node(
    query_version: Version,
    node: <A::Node as Node>::Pointer,
    list: &'a SkipList<K, V, A>,
    raw_key: Option<&'a [u8]>,
    key: Option<K::Ref<'a>>,
  ) -> VersionedEntryRef<'a, K, V, A> {
    unsafe {
      let (raw_value, vp) = node.get_value_with_pointer(&list.arena);

      let key = match key {
        Some(key) => LazyRef::with_raw(
          key,
          match raw_key {
            Some(raw_key) => raw_key,
            None => node.get_key(&list.arena),
          },
        ),
        None => LazyRef::from_raw(match raw_key {
          Some(raw_key) => raw_key,
          None => node.get_key(&list.arena),
        }),
      };

      VersionedEntryRef {
        list,
        key,
        value: raw_value.map(|raw_value| LazyRef::from_raw(raw_value)),
        value_part_pointer: vp,
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
    list: &'a SkipList<K, V, A>,
    pointer: ValuePartPointer,
    raw_key: Option<&'a [u8]>,
    key: Option<K::Ref<'a>>,
  ) -> VersionedEntryRef<'a, K, V, A> {
    unsafe {
      let raw_value =
        node.get_value_by_value_offset(&list.arena, pointer.value_offset, pointer.value_len);

      let key = match key {
        Some(key) => LazyRef::with_raw(
          key,
          match raw_key {
            Some(raw_key) => raw_key,
            None => node.get_key(&list.arena),
          },
        ),
        None => LazyRef::from_raw(match raw_key {
          Some(raw_key) => raw_key,
          None => node.get_key(&list.arena),
        }),
      };

      VersionedEntryRef {
        list,
        key,
        value: raw_value.map(|raw_value| LazyRef::from_raw(raw_value)),
        value_part_pointer: pointer,
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
pub struct EntryRef<'a, K, V, A>(pub(crate) VersionedEntryRef<'a, K, V, A>)
where
  K: Type + ?Sized,
  V: Type + ?Sized,
  A: Allocator;

impl<K, V, A> core::fmt::Debug for EntryRef<'_, K, V, A>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  A: Allocator,
{
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("EntryRef")
      .field("key", &self.key())
      .field("value", &self.value())
      .finish()
  }
}

impl<'a, K, V, A: Allocator> Clone for EntryRef<'a, K, V, A>
where
  K: ?Sized + Type,
  K::Ref<'a>: Clone,
  V: ?Sized + Type,
  V::Ref<'a>: Clone,
  A: Allocator,
{
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<'a, K, V, A: Allocator> EntryRef<'a, K, V, A>
where
  K: ?Sized + Type,
  K::Ref<'a>: KeyRef<'a, K>,
  V: ?Sized + Type,
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

impl<K, V, A> EntryRef<'_, K, V, A>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  A: Allocator,
  A::Node: WithVersion,
{
  /// Returns the version of the entry
  #[inline]
  pub fn version(&self) -> Version {
    self.0.version()
  }
}

impl<'a, K, V, A: Allocator> EntryRef<'a, K, V, A>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  A: Allocator,
{
  /// Returns the reference to the key
  #[inline]
  pub fn key(&self) -> &K::Ref<'a> {
    self.0.key()
  }

  /// Returns the key in raw bytes
  #[inline]
  pub fn raw_key(&self) -> &'a [u8] {
    self.0.raw_key()
  }

  /// Returns the reference to the value, `None` means the entry is removed.
  #[inline]
  pub fn value(&self) -> &V::Ref<'a> {
    self.0.value().expect("EntryRef's value cannot be `None`")
  }

  /// Returns the value in raw bytes
  #[inline]
  pub fn raw_value(&self) -> &'a [u8] {
    self
      .0
      .raw_value()
      .expect("EntryRef's raw value cannot be `None`")
  }
}
