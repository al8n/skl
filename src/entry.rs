use core::cell::OnceCell;

use dbutils::traits::Type;

use crate::{
  allocator::{Allocator, Node, NodePointer, ValuePartPointer, WithTrailer, WithVersion},
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
  pub(super) arena: &'a A,
  pub(super) raw_key: &'a [u8],
  pub(super) key: OnceCell<K::Ref<'a>>,
  pub(super) raw_value: Option<&'a [u8]>,
  pub(super) value: OnceCell<V::Ref<'a>>,
  pub(super) value_part_pointer: ValuePartPointer<A::Trailer>,
  pub(super) trailer: OnceCell<&'a A::Trailer>,
  pub(super) version: Version,
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
      arena: self.arena,
      raw_key: self.raw_key,
      key: self.key.clone(),
      raw_value: self.raw_value,
      value: self.value.clone(),
      value_part_pointer: self.value_part_pointer,
      trailer: self.trailer.clone(),
      version: self.version,
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
          .get_trailer_by_offset(self.arena, self.value_part_pointer.trailer_offset)
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
    node: <A::Node as Node>::Pointer,
    arena: &'a A,
  ) -> VersionedEntryRef<'a, K, V, A> {
    unsafe {
      let vp = node.trailer_offset_and_value_size();
      let raw_value = node.get_value_by_value_offset(arena, vp.value_offset, vp.value_len);

      let raw_key = node.get_key(arena);
      VersionedEntryRef {
        arena,
        raw_key,
        key: OnceCell::new(),
        raw_value,
        value: OnceCell::new(),
        value_part_pointer: vp,
        trailer: OnceCell::new(),
        version: node.version(),
        ptr: node,
      }
    }
  }

  #[inline]
  pub(crate) fn from_node_with_pointer(
    node: <A::Node as Node>::Pointer,
    arena: &'a A,
    pointer: ValuePartPointer<A::Trailer>,
  ) -> VersionedEntryRef<'a, K, V, A> {
    unsafe {
      let raw_value =
        node.get_value_by_value_offset(arena, pointer.value_offset, pointer.value_len);

      let raw_key = node.get_key(arena);
      VersionedEntryRef {
        arena,
        raw_key,
        key: OnceCell::new(),
        raw_value,
        value: OnceCell::new(),
        value_part_pointer: pointer,
        trailer: OnceCell::new(),
        version: node.version(),
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