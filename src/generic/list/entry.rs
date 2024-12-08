use core::marker::PhantomData;

use dbutils::{
  equivalentor::TypeRefComparator,
  types::{LazyRef, Type},
};

use super::{RefCounter, SkipList};
use crate::{
  allocator::{Allocator, Node, NodePointer, WithVersion},
  generic::{Active, MaybeTombstone, State},
  types::internal::ValuePointer,
  Version,
};

/// An entry reference of the `SkipMap`.
pub struct EntryRef<'a, K, V, S, A, R, C>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  A: Allocator,
  R: RefCounter,
  S: State<'a>,
{
  pub(super) list: &'a SkipList<K, V, A, R, C>,
  pub(super) key: LazyRef<'a, K>,
  pub(super) value: S::Value<V>,
  pub(super) value_part_pointer: ValuePointer,
  pub(super) version: Version,
  pub(super) query_version: Version,
  pub(super) ptr: <A::Node as Node>::Pointer,
  _m: PhantomData<S>,
}

impl<'a, K, V, S, A, R, C> core::fmt::Debug for EntryRef<'a, K, V, S, A, R, C>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  A: Allocator,
  R: RefCounter,
  S: State<'a>,
  S::Output<V>: core::fmt::Debug,
{
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("EntryRef")
      .field("key", &self.key())
      .field("value", &self.value())
      .field("version", &self.version)
      .finish()
  }
}

impl<'a, K, V, S, A, R, C> Clone for EntryRef<'a, K, V, S, A, R, C>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  A: Allocator,
  R: RefCounter,
  S: State<'a>,
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
      _m: PhantomData,
    }
  }
}

impl<'a, K, V, A, R, C> EntryRef<'a, K, V, MaybeTombstone, A, R, C>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  A: Allocator,
  R: RefCounter,
{
  #[inline]
  pub(super) fn into_active(self) -> EntryRef<'a, K, V, Active, A, R, C> {
    EntryRef {
      list: self.list,
      key: self.key,
      value: self.value.expect("try convert a tombstone to active"),
      value_part_pointer: self.value_part_pointer,
      version: self.version,
      query_version: self.query_version,
      ptr: self.ptr,
      _m: PhantomData,
    }
  }
}

impl<'a, K, V, S, A, R, C> EntryRef<'a, K, V, S, A, R, C>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  A: Allocator,
  R: RefCounter,
  S: State<'a>,
{
  /// Returns the comparator.
  #[inline]
  pub const fn comparator(&self) -> &C {
    self.list.comparator()
  }

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
  pub fn value(&self) -> S::Output<V> {
    S::output(&self.value)
  }

  /// Returns the value in raw bytes
  #[inline]
  pub fn raw_value(&self) -> Option<&'a [u8]> {
    S::raw(&self.value)
  }

  /// Returns if the entry is marked as removed
  #[inline]
  pub fn is_tombstone(&self) -> bool {
    S::is_tombstone(&self.value)
  }
}

impl<'a, K, V, S, A, R, C> EntryRef<'a, K, V, S, A, R, C>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  S: State<'a>,
  A: Allocator,
  R: RefCounter,
  C: TypeRefComparator<'a, K>,
{
  /// Returns the next entry in the map.
  #[inline]
  pub fn next(&self) -> Option<Self> {
    self.next_in(S::ALL_VERSIONS)
  }

  /// Returns the previous entry in the map.
  #[inline]
  pub fn prev(&self) -> Option<Self> {
    self.prev_in(S::ALL_VERSIONS)
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

impl<'a, K, V, S, A, R, C> EntryRef<'a, K, V, S, A, R, C>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  S: State<'a>,
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

impl<'a, K, V, S, A, R, C> EntryRef<'a, K, V, S, A, R, C>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  S: State<'a>,
  A: Allocator,
  R: RefCounter,
{
  #[inline]
  pub(crate) fn from_node(
    query_version: Version,
    node: <A::Node as Node>::Pointer,
    list: &'a SkipList<K, V, A, R, C>,
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
        value: S::from_bytes_to_value(raw_value),
        value_part_pointer: vp,
        version: node.version(),
        query_version,
        ptr: node,
        _m: PhantomData,
      }
    }
  }

  #[inline]
  pub(crate) fn from_node_with_pointer(
    query_version: Version,
    node: <A::Node as Node>::Pointer,
    list: &'a SkipList<K, V, A, R, C>,
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
        value: S::from_bytes_to_value(raw_value),
        value_part_pointer: pointer,
        version: node.version(),
        query_version,
        ptr: node,
        _m: PhantomData,
      }
    }
  }
}
