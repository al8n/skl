use crate::{
  allocator::{Allocator, Node, NodePointer, WithVersion},
  dynamic::list::SkipList,
  ref_counter::RefCounter,
  Active, MaybeTombstone, State, Transformable, Version,
};
use dbutils::equivalentor::BytesComparator;

/// An entry reference of the `SkipMap`.
pub struct EntryRef<'a, S, C, A, R>
where
  A: Allocator,
  R: RefCounter,
  S: State,
{
  pub(super) list: &'a SkipList<C, A, R>,
  pub(super) key: &'a [u8],
  pub(super) value: S::Data<'a, &'a [u8]>,
  pub(super) version: Version,
  pub(super) query_version: Version,
  pub(super) ptr: <A::Node as Node>::Pointer,
}

impl<'a, S, C, A, R> core::fmt::Debug for EntryRef<'a, S, C, A, R>
where
  A: Allocator,
  R: RefCounter,
  S: State,
  S::Data<'a, &'a [u8]>: core::fmt::Debug,
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
  S: State,
  S::Data<'a, &'a [u8]>: Clone,
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

impl<'a, S, C, A, R> Copy for EntryRef<'a, S, C, A, R>
where
  A: Allocator,
  R: RefCounter,
  S: State,
  S::Data<'a, &'a [u8]>: Copy,
{
}

impl<'a, C, A, R> EntryRef<'a, MaybeTombstone, C, A, R>
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
  S: State,
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
  pub fn value(&self) -> <S::Data<'a, &'a [u8]> as Transformable>::Output
  where
    S::Data<'a, &'a [u8]>: Transformable,
  {
    self.value.transform()
  }

  /// Returns `true` if the entry is marked as removed
  #[inline]
  pub fn tombstone(&self) -> bool
  where
    S::Data<'a, &'a [u8]>: Transformable,
  {
    !S::validate_data(&self.value)
  }
}

impl<'a, S, C, A, R> EntryRef<'a, S, C, A, R>
where
  C: BytesComparator,
  A: Allocator,
  R: RefCounter,
  S: State,
  S::Data<'a, &'a [u8]>: Sized + Transformable<Input = Option<&'a [u8]>>,
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

impl<S, C, A, R> EntryRef<'_, S, C, A, R>
where
  A: Allocator,
  A::Node: WithVersion,
  R: RefCounter,
  S: State,
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
  S: State,
{
  #[inline]
  pub(crate) fn from_node(
    query_version: Version,
    node: <A::Node as Node>::Pointer,
    list: &'a SkipList<C, A, R>,
    key: Option<&'a [u8]>,
    value: S::Data<'a, &'a [u8]>,
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
    list: &'a SkipList<C, A, R>,
    key: Option<&'a [u8]>,
    value: S::Data<'a, &'a [u8]>,
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
