use dbutils::{
  equivalentor::TypeRefComparator,
  types::{LazyRef, Type},
};

use super::{RefCounter, SkipList};
use crate::{
  allocator::{Allocator, Node, NodePointer, WithVersion},
  generic::GenericValue,
  types::internal::ValuePointer,
  Version,
};

/// An entry reference of the `SkipMap`.
pub struct EntryRef<'a, K, V, A, R, C>
where
  K: ?Sized + Type,
  V: GenericValue<'a>,
  A: Allocator,
  R: RefCounter,
{
  pub(super) list: &'a SkipList<K, V::Value, A, R, C>,
  pub(super) key: LazyRef<'a, K>,
  pub(super) value: V,
  pub(super) value_part_pointer: ValuePointer,
  pub(super) version: Version,
  pub(super) query_version: Version,
  pub(super) ptr: <A::Node as Node>::Pointer,
}

impl<'a, K, V, A, R, C> core::fmt::Debug for EntryRef<'a, K, V, A, R, C>
where
  K: ?Sized + Type,
  V: GenericValue<'a>,
  V::Ref: core::fmt::Debug,
  A: Allocator,
  R: RefCounter,
{
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("EntryRef")
      .field("key", &self.key())
      .field("value", &self.value())
      .field("version", &self.version)
      .finish()
  }
}

impl<'a, K, V, A, R, C> Clone for EntryRef<'a, K, V, A, R, C>
where
  K: ?Sized + Type,
  K::Ref<'a>: Clone,
  V: GenericValue<'a> + Clone,
  A: Allocator,
  R: RefCounter,
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

impl<'a, K, V, A, R, C> EntryRef<'a, K, Option<LazyRef<'a, V>>, A, R, C>
where
  K: ?Sized + Type,
  K::Ref<'a>: Clone,
  V: ?Sized + Type,
  A: Allocator,
  R: RefCounter,
{
  #[inline]
  pub(super) fn map<NV>(self) -> EntryRef<'a, K, NV, A, R, C>
  where
    NV: GenericValue<'a, Value = V> + 'a,
  {
    EntryRef {
      list: self.list,
      key: self.key,
      value: NV::from_lazy_ref(self.value),
      value_part_pointer: self.value_part_pointer,
      version: self.version,
      query_version: self.query_version,
      ptr: self.ptr,
    }
  }
}

impl<'a, K, V, A, R, C> EntryRef<'a, K, V, A, R, C>
where
  K: ?Sized + Type,
  V: GenericValue<'a>,
  A: Allocator,
  R: RefCounter,
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
  pub fn value(&self) -> V::Ref {
    self.value.as_ref()
  }

  /// Returns the value in raw bytes
  #[inline]
  pub fn raw_value(&self) -> Option<&'a [u8]> {
    self.value.raw()
  }

  /// Returns if the entry is marked as removed
  #[inline]
  pub fn is_removed(&self) -> bool {
    self.value.is_removed()
  }
}

impl<'a, K, V, A, R, C> EntryRef<'a, K, V, A, R, C>
where
  K: ?Sized + Type,

  V: GenericValue<'a> + 'a,
  A: Allocator,
  R: RefCounter,
  C: TypeRefComparator<'a, Type = K>,
{
  /// Returns the next entry in the map.
  #[inline]
  pub fn next(&self) -> Option<Self> {
    self.next_in(self.value.all_versions())
  }

  /// Returns the previous entry in the map.
  #[inline]
  pub fn prev(&self) -> Option<Self> {
    self.prev_in(self.value.all_versions())
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

impl<'a, K, V, A, R, C> EntryRef<'a, K, V, A, R, C>
where
  K: ?Sized + Type,
  V: GenericValue<'a>,
  A: Allocator,
  A::Node: WithVersion,
  R: RefCounter,
{
  /// Returns the version of the entry
  #[inline]
  pub fn version(&self) -> Version {
    self.version
  }
}

impl<'a, K, V, A, R, C> EntryRef<'a, K, V, A, R, C>
where
  K: ?Sized + Type,
  V: GenericValue<'a> + 'a,
  A: Allocator,
  R: RefCounter,
{
  #[inline]
  pub(crate) fn from_node(
    query_version: Version,
    node: <A::Node as Node>::Pointer,
    list: &'a SkipList<K, V::Value, A, R, C>,
    raw_key: Option<&'a [u8]>,
    key: Option<K::Ref<'a>>,
  ) -> Self {
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

      Self {
        list,
        key,
        value: V::from_bytes(raw_value),
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
    list: &'a SkipList<K, V::Value, A, R, C>,
    pointer: ValuePointer,
    raw_key: Option<&'a [u8]>,
    key: Option<K::Ref<'a>>,
  ) -> Self {
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

      Self {
        list,
        key,
        value: V::from_bytes(raw_value),
        value_part_pointer: pointer,
        version: node.version(),
        query_version,
        ptr: node,
      }
    }
  }
}
