use crate::{
  allocator::{Allocator, Node, NodePointer, WithVersion},
  dynamic::{list::SkipList, Value},
  ref_counter::RefCounter,
  Version,
};
use dbutils::equivalentor::DynComparator;

/// An entry reference of the `SkipMap`.
pub struct EntryRef<'a, V, C, A, R>
where
  A: Allocator,
  R: RefCounter,
{
  pub(super) list: &'a SkipList<A, R, C>,
  pub(super) key: &'a [u8],
  pub(super) value: V,
  pub(super) version: Version,
  pub(super) query_version: Version,
  pub(super) ptr: <A::Node as Node>::Pointer,
}

impl<V, C, A, R> core::fmt::Debug for EntryRef<'_, V, C, A, R>
where
  A: Allocator,
  R: RefCounter,
  V: core::fmt::Debug,
{
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("EntryRef")
      .field("key", &self.key())
      .field("value", &self.value)
      .field("version", &self.version)
      .finish()
  }
}

impl<V, C, A, R> Clone for EntryRef<'_, V, C, A, R>
where
  A: Allocator,
  R: RefCounter,
  V: Clone,
{
  #[inline]
  fn clone(&self) -> Self {
    Self {
      list: self.list,
      key: self.key,
      value: self.value.clone(),
      version: self.version,
      query_version: self.query_version,
      ptr: self.ptr,
    }
  }
}

impl<V, C, A, R> Copy for EntryRef<'_, V, C, A, R>
where
  A: Allocator,
  R: RefCounter,
  V: Copy,
{
}

impl<'a, A, R, C> EntryRef<'a, Option<&'a [u8]>, C, A, R>
where
  A: Allocator,
  R: RefCounter,
{
  #[inline]
  pub(super) fn map<NV>(self) -> EntryRef<'a, NV, C, A, R>
  where
    NV: Value<'a> + 'a,
  {
    EntryRef {
      list: self.list,
      key: self.key,
      value: NV::from_value_bytes(self.value),
      version: self.version,
      query_version: self.query_version,
      ptr: self.ptr,
    }
  }
}

impl<'a, V, C, A, R> EntryRef<'a, V, C, A, R>
where
  A: Allocator,
  R: RefCounter,
{
  /// Returns the comparator.
  #[inline]
  pub const fn comparator(&self) -> &C {
    self.list.comparator()
  }

  /// Returns the reference to the key
  #[inline]
  pub const fn key(&self) -> &'a [u8] {
    self.key
  }

  /// Returns the reference to the value, `None` means the entry is removed.
  #[inline]
  pub fn value(&self) -> V::Ref
  where
    V: Value<'a>,
  {
    self.value.as_ref()
  }

  /// Returns if the entry is marked as removed
  #[inline]
  pub fn is_removed(&self) -> bool
  where
    V: Value<'a>,
  {
    self.value.is_removed()
  }
}

impl<'a, V, C, A, R> EntryRef<'a, V, C, A, R>
where
  C: DynComparator<[u8], [u8]>,
  A: Allocator,
  R: RefCounter,
  V: Value<'a> + 'a,
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
          .map(|ent| ent.map())
      }
    } else {
      unsafe {
        nd = self.list.get_next(nd, 0);
        self
          .list
          .move_to_next_maximum_version(&mut nd, self.query_version, |_| true)
          .map(|ent| ent.map())
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
          .map(|ent| ent.map())
      }
    }
  }
}

impl<V, C, A, R> EntryRef<'_, V, C, A, R>
where
  A: Allocator,
  A::Node: WithVersion,
  R: RefCounter,
{
  /// Returns the version of the entry
  #[inline]
  pub const fn version(&self) -> Version {
    self.version
  }
}

impl<'a, V, C, A, R> EntryRef<'a, V, C, A, R>
where
  A: Allocator,
  R: RefCounter,
{
  #[inline]
  pub(crate) fn from_node(
    query_version: Version,
    node: <A::Node as Node>::Pointer,
    list: &'a SkipList<A, R, C>,
    key: Option<&'a [u8]>,
    value: V,
  ) -> Self {
    unsafe {
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
    list: &'a SkipList<A, R, C>,
    key: Option<&'a [u8]>,
    value: V,
  ) -> Self {
    unsafe {
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
