use crate::allocator::{WithTrailer, WithVersion};

use super::*;

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
  pub(super) key: K::Ref<'a>,
  pub(super) value: Option<V::Ref<'a>>,
  pub(super) value_part_pointer: ValuePartPointer<A::Trailer>,
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
      value: self.value.clone(),
      value_part_pointer: self.value_part_pointer,
      version: self.version,
      ptr: self.ptr,
    }
  }
}

impl<'a, K, V, A: Allocator> Copy for VersionedEntryRef<'a, K, V, A>
where
  K: ?Sized + Type,
  K::Ref<'a>: Copy,
  V: ?Sized + Type,
  V::Ref<'a>: Copy,
  A: Allocator,
{
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
      let trailer = self
        .ptr
        .get_trailer_by_offset(self.arena, self.value_part_pointer.trailer_offset);
      trailer
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
  pub const fn key(&self) -> &K::Ref<'a> {
    &self.key
  }

  /// Returns the reference to the value, `None` means the entry is removed.
  #[inline]
  pub fn value(&self) -> Option<&V::Ref<'a>> {
    self.value.as_ref()
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
      let value = node
        .get_value_by_value_offset(arena, vp.value_offset, vp.value_len)
        .map(ty_ref::<V>);

      let raw_key = node.get_key(arena);
      VersionedEntryRef {
        key: <K::Ref<'_> as TypeRef<'_>>::from_slice(raw_key),
        raw_key,
        value,
        value_part_pointer: vp,
        arena,
        ptr: node,
        version: node.version(),
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
      let value = node
        .get_value_by_value_offset(arena, pointer.value_offset, pointer.value_len)
        .map(ty_ref::<V>);

      let raw_key = node.get_key(arena);
      VersionedEntryRef {
        key: <K::Ref<'_> as TypeRef<'_>>::from_slice(raw_key),
        raw_key,
        value,
        value_part_pointer: pointer,
        arena,
        ptr: node,
        version: node.version(),
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

impl<'a, K, V, A: Allocator> Copy for EntryRef<'a, K, V, A>
where
  K: ?Sized + Type,
  K::Ref<'a>: Copy,
  V: ?Sized + Type,
  V::Ref<'a>: Copy,
  A: Allocator,
{
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
  pub const fn key(&self) -> &K::Ref<'a> {
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
