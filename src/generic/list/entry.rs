use dbutils::{
  equivalentor::TypeRefComparator,
  types::{LazyRef, Type},
};

use super::{RefCounter, SkipList};
use crate::{
  allocator::{Allocator, Node, NodePointer, WithVersion},
  generic::{Active, MaybeTombstone, State},
  types::internal::ValuePointer,
  Transfer, Version,
};

/// An entry reference of the `SkipMap`.
pub struct EntryRef<'a, K, V, S, C, A, R>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  A: Allocator,
  R: RefCounter,
  S: State,
{
  pub(super) list: &'a SkipList<K, V, C, A, R>,
  pub(super) key: LazyRef<'a, K>,
  pub(super) value: S::Data<'a, LazyRef<'a, V>>,
  pub(super) value_part_pointer: ValuePointer,
  pub(super) version: Version,
  pub(super) query_version: Version,
  pub(super) ptr: <A::Node as Node>::Pointer,
}

impl<'a, K, V, S, C, A, R> core::fmt::Debug for EntryRef<'a, K, V, S, C, A, R>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  A: Allocator,
  R: RefCounter,
  S: Transfer<'a, LazyRef<'a, V>>,
  S::Data<'a, S::To>: core::fmt::Debug,
{
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("EntryRef")
      .field("key", &self.key())
      .field("value", &self.value())
      .field("version", &self.version)
      .finish()
  }
}

impl<'a, K, V, S, C, A, R> Clone for EntryRef<'a, K, V, S, C, A, R>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  A: Allocator,
  R: RefCounter,
  S: State,
  S::Data<'a, LazyRef<'a, V>>: Sized + Clone,
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

impl<'a, K, V, C, A, R> EntryRef<'a, K, V, MaybeTombstone, C, A, R>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  A: Allocator,
  R: RefCounter,
{
  #[inline]
  pub(super) fn into_active(self) -> EntryRef<'a, K, V, Active, C, A, R> {
    EntryRef {
      list: self.list,
      key: self.key,
      value: self.value.expect("entry in Active state must have value"),
      value_part_pointer: self.value_part_pointer,
      version: self.version,
      query_version: self.query_version,
      ptr: self.ptr,
    }
  }
}

impl<'a, K, V, S, C, A, R> EntryRef<'a, K, V, S, C, A, R>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  A: Allocator,
  R: RefCounter,
  S: State,
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
  pub fn value(&self) -> S::Data<'a, S::To>
  where
    S: Transfer<'a, LazyRef<'a, V>>,
  {
    S::transfer(&self.value)
  }

  /// Returns the value in raw bytes
  #[inline]
  pub fn raw_value(&self) -> S::Data<'a, &'a [u8]>
  where
    S: Transfer<'a, LazyRef<'a, V>>,
  {
    S::input(&self.value)
  }

  /// Returns `true` if the entry is marked as removed
  #[inline]
  pub fn tombstone(&self) -> bool
  where
    S: Transfer<'a, LazyRef<'a, V>>,
  {
    !S::validate_data(&self.value)
  }
}

impl<'a, K, V, S, C, A, R> EntryRef<'a, K, V, S, C, A, R>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  S: Transfer<'a, LazyRef<'a, V>>,
  A: Allocator,
  R: RefCounter,
  C: TypeRefComparator<'a, K>,
{
  /// Returns the next entry in the map.
  #[inline]
  pub fn next(&self) -> Option<Self> {
    self.next_in(S::ALWAYS_VALID)
  }

  /// Returns the previous entry in the map.
  #[inline]
  pub fn prev(&self) -> Option<Self> {
    self.prev_in(S::ALWAYS_VALID)
  }

  fn next_in(&self, always_valid: bool) -> Option<Self> {
    let mut nd = self.ptr;
    if !always_valid {
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

  fn prev_in(&self, always_valid: bool) -> Option<Self> {
    let mut nd = self.ptr;
    if !always_valid {
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

impl<K, V, S, C, A, R> EntryRef<'_, K, V, S, C, A, R>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  S: State,
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

impl<'a, K, V, S, C, A, R> EntryRef<'a, K, V, S, C, A, R>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  S: Transfer<'a, LazyRef<'a, V>>,
  A: Allocator,
  R: RefCounter,
{
  #[inline]
  pub(crate) fn from_node(
    query_version: Version,
    node: <A::Node as Node>::Pointer,
    list: &'a SkipList<K, V, C, A, R>,
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
        value: S::from_input(raw_value),
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
    list: &'a SkipList<K, V, C, A, R>,
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
        value: S::from_input(raw_value),
        value_part_pointer: pointer,
        version: node.version(),
        query_version,
        ptr: node,
      }
    }
  }
}
