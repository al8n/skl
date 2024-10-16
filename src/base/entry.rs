use core::cell::OnceCell;

use dbutils::traits::{KeyRef, Type};

use crate::{
  allocator::{Allocator, Node, NodePointer, ValuePartPointer, WithTrailer, WithVersion},
  base::SkipList,
  ty_ref, Version,
};

/// A versioned entry reference of the skipmap.
///
/// Compared to the [`EntryRef`], this one's value can be `None` which means the entry is removed.
#[derive(Debug)]
pub struct VersionedEntryRef<'a, K, V, A>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  A: Allocator,
{
  pub(super) list: &'a SkipList<K, V, A>,
  pub(super) raw_key: &'a [u8],
  pub(super) key: OnceCell<K::Ref<'a>>,
  pub(super) raw_value: Option<&'a [u8]>,
  pub(super) value: OnceCell<V::Ref<'a>>,
  pub(super) value_part_pointer: ValuePartPointer<A::Trailer>,
  pub(super) trailer: OnceCell<&'a A::Trailer>,
  pub(super) version: Version,
  pub(super) query_version: Version,
  pub(super) ptr: <A::Node as Node>::Pointer,
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
      raw_key: self.raw_key,
      key: self.key.clone(),
      raw_value: self.raw_value,
      value: self.value.clone(),
      value_part_pointer: self.value_part_pointer,
      trailer: self.trailer.clone(),
      version: self.version,
      query_version: self.query_version,
      ptr: self.ptr,
    }
  }
}

impl<'a, K, V, A> VersionedEntryRef<'a, K, V, A>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  A: Allocator,
  A::Node: WithTrailer,
{
  /// Returns the trailer of the entry
  #[inline]
  pub fn trailer(&self) -> &'a A::Trailer {
    unsafe {
      self.trailer.get_or_init(|| {
        self
          .ptr
          .get_trailer_by_offset(&self.list.arena, self.value_part_pointer.trailer_offset)
      })
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
    self.key.get_or_init(|| ty_ref::<K>(self.raw_key))
  }

  /// Returns the reference to the value, `None` means the entry is removed.
  #[inline]
  pub fn value(&self) -> Option<&V::Ref<'a>> {
    self
      .raw_value
      .map(|raw_value| self.value.get_or_init(|| ty_ref::<V>(raw_value)))
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
    self.next_in(true, false)
  }

  /// Returns the previous entry in the map.
  #[inline]
  pub fn prev(&self) -> Option<Self> {
    self.prev_in(true, false)
  }

  fn next_in(&self, all_versions: bool, ignore_invalid_trailer: bool) -> Option<Self> {
    loop {
      unsafe {
        let nd = self.list.get_next(self.ptr, 0, ignore_invalid_trailer);

        if nd.is_null() || nd.offset() == self.list.tail.offset() {
          return None;
        }

        let (value, pointer) = nd.get_value_and_trailer_with_pointer(&self.list.arena);
        if nd.version() > self.query_version {
          continue;
        }

        if !all_versions && value.is_none() {
          continue;
        }

        let nk = ty_ref::<K>(nd.get_key(&self.list.arena));
        if !all_versions && self.key().eq(&nk) {
          continue;
        }

        let ent =
          VersionedEntryRef::from_node_with_pointer(self.query_version, nd, self.list, pointer);
        return Some(ent);
      }
    }
  }

  fn prev_in(&self, all_versions: bool, ignore_invalid_trailer: bool) -> Option<Self> {
    loop {
      unsafe {
        let nd = self.list.get_prev(self.ptr, 0, !ignore_invalid_trailer);

        if nd.is_null() || nd.offset() == self.list.head.offset() {
          return None;
        }

        let (value, pointer) = nd.get_value_and_trailer_with_pointer(&self.list.arena);
        if nd.version() > self.query_version {
          continue;
        }

        if !all_versions && value.is_none() {
          continue;
        }

        let nk = ty_ref::<K>(nd.get_key(&self.list.arena));
        if !all_versions && self.key().eq(&nk) {
          continue;
        }

        let ent =
          VersionedEntryRef::from_node_with_pointer(self.query_version, nd, self.list, pointer);
        return Some(ent);
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
  ) -> VersionedEntryRef<'a, K, V, A> {
    unsafe {
      let vp = node.trailer_offset_and_value_size();
      let raw_value = node.get_value_by_value_offset(&list.arena, vp.value_offset, vp.value_len);

      let raw_key = node.get_key(&list.arena);
      VersionedEntryRef {
        list,
        raw_key,
        key: OnceCell::new(),
        raw_value,
        value: OnceCell::new(),
        value_part_pointer: vp,
        trailer: OnceCell::new(),
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
    pointer: ValuePartPointer<A::Trailer>,
  ) -> VersionedEntryRef<'a, K, V, A> {
    unsafe {
      let raw_value =
        node.get_value_by_value_offset(&list.arena, pointer.value_offset, pointer.value_len);

      let raw_key = node.get_key(&list.arena);
      VersionedEntryRef {
        list,
        raw_key,
        key: OnceCell::new(),
        raw_value,
        value: OnceCell::new(),
        value_part_pointer: pointer,
        trailer: OnceCell::new(),
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
#[derive(Debug)]
pub struct EntryRef<'a, K, V, A>(pub(crate) VersionedEntryRef<'a, K, V, A>)
where
  K: Type + ?Sized,
  V: Type + ?Sized,
  A: Allocator;

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

impl<'a, K, V, A> EntryRef<'a, K, V, A>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  A: Allocator,
  A::Node: WithTrailer,
{
  /// Returns the trailer of the entry
  #[inline]
  pub fn trailer(&'a self) -> &'a A::Trailer {
    self.0.trailer()
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
    self.0.next_in(false, true).map(Self)
  }

  /// Returns the previous entry in the map.
  #[inline]
  pub fn prev(&self) -> Option<Self> {
    self.0.prev_in(false, true).map(Self)
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

  /// Returns the reference to the value, `None` means the entry is removed.
  #[inline]
  pub fn value(&self) -> &V::Ref<'a> {
    match self.0.value() {
      Some(value) => value,
      None => panic!("EntryRef's value cannot be `None`"),
    }
  }
}
