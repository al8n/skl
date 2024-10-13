use dbutils::traits::{Type, TypeRef};

use super::*;

/// A versioned entry reference of the skipmap.
///
/// Compared to the [`EntryRef`], this one's value can be `None` which means the entry is removed.
#[derive(Debug)]
pub struct GenericVersionedEntryRef<'a, K, V, A: Allocator>
where
  K: Type + ?Sized,
  V: Type + ?Sized,
{
  pub(super) arena: &'a A,
  pub(super) key: K::Ref<'a>,
  pub(super) value: Option<V::Ref<'a>>,
  pub(super) value_part_pointer: ValuePartPointer<A::Trailer>,
  pub(super) version: Version,
  pub(super) ptr: <A::Node as Node>::Pointer,
}

impl<'a, K, V, A> From<VersionedEntryRef<'a, A>> for GenericVersionedEntryRef<'a, K, V, A>
where
  K: Type + ?Sized,
  V: Type + ?Sized,
  A: Allocator,
{
  fn from(value: VersionedEntryRef<'a, A>) -> Self {
    let VersionedEntryRef {
      arena,
      key,
      value_part_pointer,
      ptr: node,
      version,
    } = value;

    unsafe {
      let vp = node.trailer_offset_and_value_size();
      let value = node.get_value_by_value_offset(
        arena,
        vp.value_offset,
        vp.value_len,
      ).map(|src| <V::Ref<'_> as TypeRef<'_>>::from_slice(src));
      let key = <K::Ref<'_> as TypeRef<'_>>::from_slice(key);
      Self {
        arena,
        key,
        value,
        value_part_pointer,
        version,
        ptr: node,
      }
    }
  }
}

impl<'a, K, V, A: Allocator> Clone for GenericVersionedEntryRef<'a, K, V, A>
where
  K: Type + ?Sized,
  K::Ref<'a>: Clone,
  V: Type + ?Sized,
  V::Ref<'a>: Clone,
{
  fn clone(&self) -> Self {
    Self {
      arena: self.arena,
      key: self.key.clone(),
      value: self.value.clone(),
      value_part_pointer: self.value_part_pointer,
      version: self.version,
      ptr: self.ptr,
    }
  }
}

impl<'a, K, V, A: Allocator> Copy for GenericVersionedEntryRef<'a, K, V, A>
where
  K: Type + ?Sized,
  K::Ref<'a>: Copy,
  V: Type + ?Sized,
  V::Ref<'a>: Copy,
{}

impl<'a, K, V, A> GenericVersionedEntryRef<'a, K, V, A>
where
  K: Type + ?Sized,
  V: Type + ?Sized,
  A: Allocator,
  A::Node: WithTrailer,
{
  /// Returns the trailer of the entry
  #[inline]
  pub fn trailer(&'a self) -> &'a A::Trailer {
    unsafe {
      let trailer = self
        .ptr
        .get_trailer_by_offset(self.arena, self.value_part_pointer.trailer_offset);
      trailer
    }
  }
}

impl<'a, K, V, A: Allocator> GenericVersionedEntryRef<'a, K, V, A>
where
  K: Type + ?Sized,
  V: Type + ?Sized,
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

  /// Returns the version of the entry
  #[inline]
  pub fn version(&self) -> Version {
    self.version
  }
}


impl<'a, K, V, A: Allocator> GenericVersionedEntryRef<'a, K, V, A>
where
  K: Type + ?Sized,
  V: Type + ?Sized,
{
  #[inline]
  pub(super) fn from_node(
    node: <A::Node as Node>::Pointer,
    arena: &'a A,
  ) -> GenericVersionedEntryRef<'a, K, V, A> {
    unsafe {
      let vp = node.trailer_offset_and_value_size();
      let value = node.get_value_by_value_offset(
        arena,
        vp.value_offset,
        vp.value_len,
      ).map(|src| <V::Ref<'_> as TypeRef<'_>>::from_slice(src));

      GenericVersionedEntryRef {
        key: <K::Ref<'_> as TypeRef<'_>>::from_slice(node.get_key(arena)),
        value,
        value_part_pointer: vp,
        arena,
        ptr: node,
        version: node.version(),
      }
    }
  }

  #[inline]
  pub(super) fn from_node_with_pointer(
    node: <A::Node as Node>::Pointer,
    arena: &'a A,
    pointer: ValuePartPointer<A::Trailer>,
  ) -> GenericVersionedEntryRef<'a, K, V, A> {
    unsafe {
      let value = node.get_value_by_value_offset(
        arena,
        pointer.value_offset,
        pointer.value_len,
      ).map(|src| <V::Ref<'_> as TypeRef<'_>>::from_slice(src));

      GenericVersionedEntryRef {
        key: <K::Ref<'_> as TypeRef<'_>>::from_slice(node.get_key(arena)),
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
/// Compared to the [`GenericVersionedEntryRef`], this one's value cannot be `None`.
#[derive(Debug)]
pub struct GenericEntryRef<'a, K, V, A: Allocator>(pub(crate) GenericVersionedEntryRef<'a, K, V, A>)
where
  K: Type + ?Sized,
  V: Type + ?Sized;

impl<'a, K, V, A: Allocator> Clone for GenericEntryRef<'a, K, V, A>
where
  K: Type + ?Sized,
  K::Ref<'a>: Clone,
  V: Type + ?Sized,
  V::Ref<'a>: Clone,
{
  #[inline]
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<'a, K, V, A: Allocator> Copy for GenericEntryRef<'a, K, V, A>
where
  K: Type + ?Sized,
  K::Ref<'a>: Copy,
  V: Type + ?Sized,
  V::Ref<'a>: Copy,
{}

impl<'a, K, V, A> GenericEntryRef<'a, K, V, A>
where
  K: Type + ?Sized,
  V: Type + ?Sized,
  A: Allocator,
{
  #[inline]
  pub(crate) fn from_entry(value: EntryRef<'a, A>) -> Self {
    Self(GenericVersionedEntryRef::from(value.0))
  }
}

impl<'a, K, V, A> GenericEntryRef<'a, K, V, A>
where
  K: Type + ?Sized,
  K::Ref<'a>: Clone,
  V: Type + ?Sized,
  V::Ref<'a>: Clone,
  A: Allocator,
  A::Node: WithTrailer,
{
  /// Returns the trailer of the entry
  #[inline]
  pub fn trailer(&'a self) -> &'a A::Trailer {
    self.0.trailer()
  }
}

impl<K, V, A> GenericEntryRef<'_, K, V, A>
where
  K: Type + ?Sized,
  V: Type + ?Sized,
  A: Allocator,
  A::Node: WithVersion,
{
  /// Returns the version of the entry
  #[inline]
  pub fn version(&self) -> Version {
    self.0.version()
  }
}

impl<'a, K, V, A: Allocator> GenericEntryRef<'a, K, V, A>
where
  K: Type + ?Sized,
  K::Ref<'a>: Clone,
  V: Type + ?Sized,
  V::Ref<'a>: Clone,
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
      None => panic!("GenericEntryRef's value cannot be `None`"),
    }
  }
}
