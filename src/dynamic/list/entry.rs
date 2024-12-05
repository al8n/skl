use crate::{
  allocator::{Allocator, Node, NodePointer, WithVersion},
  dynamic::list::SkipList,
  ref_counter::RefCounter,
  Active, MaybeTombstone, State, Version,
};
use dbutils::equivalentor::BytesComparator;

/// An entry reference of the `SkipMap`.
pub struct EntryRef<'a, S, C, A, R>
where
  A: Allocator,
  R: RefCounter,
  S: State<'a>,
{
  pub(super) list: &'a SkipList<A, R, C>,
  pub(super) key: &'a [u8],
  pub(super) value: S::BytesValue,
  pub(super) version: Version,
  pub(super) query_version: Version,
  pub(super) ptr: <A::Node as Node>::Pointer,
}

impl<'a, S, C, A, R> core::fmt::Debug for EntryRef<'a, S, C, A, R>
where
  A: Allocator,
  R: RefCounter,
  S: State<'a>,
  S::BytesValue: core::fmt::Debug,
{
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("EntryRef")
      .field("key", &self.key())
      .field("value", &self.value)
      .field("version", &self.version)
      .finish()
  }
}

impl<'a, S, C, A, R> Clone for EntryRef<'a, S, C, A, R>
where
  A: Allocator,
  R: RefCounter,
  S: State<'a>,
{
  #[inline]
  fn clone(&self) -> Self {
    *self
  }
}

impl<'a, S, C, A, R> Copy for EntryRef<'a, S, C, A, R>
where
  A: Allocator,
  R: RefCounter,
  S: State<'a>,
{
}

impl<'a, A, R, C> EntryRef<'a, MaybeTombstone, C, A, R>
where
  A: Allocator,
  R: RefCounter,
{
  #[inline]
  pub(super) fn into_active(self) -> EntryRef<'a, Active, C, A, R> {
    EntryRef {
      list: self.list,
      key: self.key,
      value: self.value.expect("try convert a tombstone entry to active"),
      version: self.version,
      query_version: self.query_version,
      ptr: self.ptr,
    }
  }
}

impl<'a, S, C, A, R> EntryRef<'a, S, C, A, R>
where
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
  pub const fn key(&self) -> &'a [u8] {
    self.key
  }

  /// Returns the reference to the value, `None` means the entry is removed.
  #[inline]
  pub fn value(&self) -> S::BytesValueOutput {
    S::bytes_output(&self.value)
  }

  /// Returns if the entry is marked as removed
  #[inline]
  pub fn is_tombstone(&self) -> bool {
    S::is_tombstone_bytes(&self.value)
  }
}

impl<'a, S, C, A, R> EntryRef<'a, S, C, A, R>
where
  C: BytesComparator,
  A: Allocator,
  R: RefCounter,
  S: State<'a>,
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

impl<'a, S, C, A, R> EntryRef<'a, S, C, A, R>
where
  A: Allocator,
  A::Node: WithVersion,
  R: RefCounter,
  S: State<'a>,
{
  /// Returns the version of the entry
  #[inline]
  pub const fn version(&self) -> Version {
    self.version
  }
}

impl<'a, S, C, A, R> EntryRef<'a, S, C, A, R>
where
  A: Allocator,
  R: RefCounter,
  S: State<'a>,
{
  #[inline]
  pub(crate) fn from_node(
    query_version: Version,
    node: <A::Node as Node>::Pointer,
    list: &'a SkipList<A, R, C>,
    key: Option<&'a [u8]>,
    value: S::BytesValue,
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
    value: S::BytesValue,
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
