use core::{
  borrow::Borrow,
  mem,
  ops::{Bound, RangeBounds},
};

use dbutils::{buffer::VacantBuffer, equivalentor::BytesComparator};
use rarena_allocator::Allocator as _;

use crate::{
  allocator::{Allocator, Meta, Node, NodePointer},
  error::Error,
  random_height,
  types::{Height, ValueBuilder},
  Header, Version,
};

use super::{iterator, EntryRef, RefCounter, SkipList};

mod update;

type RemoveValueBuilder<E> =
  ValueBuilder<std::boxed::Box<dyn Fn(&mut VacantBuffer<'_>) -> Result<usize, E>>>;

impl<A, R, C> SkipList<A, R, C>
where
  A: Allocator,
  R: RefCounter,
{
  /// Sets remove on drop, only works on mmap with a file backend.
  ///
  /// Default is `false`.
  ///
  /// > **WARNING:** Once set to `true`, the backed file will be removed when the allocator is dropped, even though the file is opened in
  /// > read-only mode.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub fn remove_on_drop(&self, val: bool) {
    self.arena.remove_on_drop(val);
  }

  /// Returns the header of the `SkipList`.
  ///
  /// By default, `SkipList` will allocate meta, head node, and tail node in the ARENA,
  /// and the data section will be allocated after the tail node.
  ///
  /// This method will return the header of the `SkipList`.
  #[inline]
  pub const fn header(&self) -> Option<&Header> {
    self.header.as_ref()
  }

  /// Returns the version number of the [`SkipList`].
  #[inline]
  pub fn version(&self) -> u16 {
    self.arena.magic_version()
  }

  /// Returns the magic version number of the [`SkipList`].
  ///
  /// This value can be used to check the compatibility for application using [`SkipList`].
  #[inline]
  pub fn magic_version(&self) -> u16 {
    self.meta().magic_version()
  }

  /// Returns the height of the highest tower within any of the nodes that
  /// have ever been allocated as part of this skiplist.
  #[inline]
  pub fn height(&self) -> u8 {
    self.meta().height()
  }

  /// Returns the number of entries in the skipmap.
  #[inline]
  pub fn len(&self) -> usize {
    self.meta().len() as usize
  }

  /// Returns true if the skipmap is empty.
  #[inline]
  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }

  /// Gets the number of pointers to this `SkipList` similar to [`Arc::strong_count`](std::sync::Arc::strong_count).
  #[inline]
  pub fn refs(&self) -> usize {
    self.arena.refs()
  }

  /// Returns the maximum version of all entries in the map.
  #[inline]
  pub fn maximum_version(&self) -> u64 {
    self.meta().maximum_version()
  }

  /// Returns the minimum version of all entries in the map.
  #[inline]
  pub fn minimum_version(&self) -> u64 {
    self.meta().minimum_version()
  }

  /// Returns `true` if the map may contain an entry whose version is less or equal to the given version.
  #[inline]
  pub fn may_contain_version(&self, version: Version) -> bool {
    self.minimum_version() <= version
  }

  /// Returns a random generated height.
  ///
  /// This method is useful when you want to check if the underlying allocator can allocate a node.
  #[inline]
  pub fn random_height(&self) -> Height {
    random_height(self.arena.options().max_height())
  }

  /// Returns the estimated size of a node with the given height and key/value sizes.
  ///
  /// **Note**: The returned size is only an estimate and may not be accurate, which means that the actual size is less than or equal to the returned size.
  #[inline]
  pub fn estimated_node_size(height: Height, key_size: usize, value_size: usize) -> usize {
    let height: usize = height.into();
    7 // max padding
      + mem::size_of::<A::Node>()
      + mem::size_of::<<A::Node as Node>::Link>() * height
      + key_size
      + value_size
  }

  /// Flushes outstanding memory map modifications to disk.
  ///
  /// When this method returns with a non-error result,
  /// all outstanding changes to a file-backed memory map are guaranteed to be durably stored.
  /// The file's metadata (including last modification timestamp) may not be updated.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn flush(&self) -> std::io::Result<()> {
    self.arena.flush()
  }

  /// Asynchronously flushes outstanding memory map modifications to disk.
  ///
  /// This method initiates flushing modified pages to durable storage, but it will not wait for
  /// the operation to complete before returning. The file's metadata (including last
  /// modification timestamp) may not be updated.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn flush_async(&self) -> std::io::Result<()> {
    self.arena.flush_async()
  }
}

impl<A, RC, C> SkipList<A, RC, C>
where
  A: Allocator,
  RC: RefCounter,
  C: BytesComparator,
{
  /// Returns `true` if the key exists in the map.
  ///
  /// This method will return `false` if the entry is marked as removed. If you want to check if the key exists even if it is marked as removed,
  /// you can use [`contains_key_versioned`](SkipList::contains_key_versioned).
  #[inline]
  pub fn contains_key(&self, version: Version, key: &[u8]) -> bool {
    self.get(version, key).is_some()
  }

  /// Returns `true` if the key exists in the map, even if it is marked as removed.
  #[inline]
  pub fn contains_key_versioned(&self, version: Version, key: &[u8]) -> bool {
    self.get_versioned(version, key).is_some()
  }

  /// Returns the first entry in the map.
  pub fn first(&self, version: Version) -> Option<EntryRef<'_, &[u8], C, A, RC>> {
    self.iter(version).next()
  }

  /// Returns the last entry in the map.
  pub fn last(&self, version: Version) -> Option<EntryRef<'_, &[u8], C, A, RC>> {
    self.iter(version).last()
  }

  /// Returns the first entry in the map.
  pub fn first_versioned(&self, version: Version) -> Option<EntryRef<'_, Option<&[u8]>, C, A, RC>> {
    self.iter_all_versions(version).next()
  }

  /// Returns the last entry in the map.
  pub fn last_versioned(&self, version: Version) -> Option<EntryRef<'_, Option<&[u8]>, C, A, RC>> {
    self.iter_all_versions(version).last()
  }

  /// Returns the value associated with the given key, if it exists.
  ///
  /// This method will return `None` if the entry is marked as removed. If you want to get the entry even if it is marked as removed,
  /// you can use [`get_versioned`](SkipList::get_versioned).
  pub fn get(&self, version: Version, key: &[u8]) -> Option<EntryRef<'_, &[u8], C, A, RC>> {
    unsafe {
      let (n, eq) = self.find_near(version, key, false, true); // findLessOrEqual.

      let node = n?;
      let raw_node_key = node.get_key(&self.arena);
      let (value, _) = node.get_value_with_pointer(&self.arena);
      if eq {
        return value.map(|value| {
          EntryRef::from_node_with_pointer(version, node, self, Some(raw_node_key), value)
        });
      }

      if !self.cmp.equivalent(key, raw_node_key) {
        return None;
      }

      if node.version() > version {
        return None;
      }

      value.map(|value| {
        EntryRef::from_node_with_pointer(version, node, self, Some(raw_node_key), value)
      })
    }
  }

  /// Returns the value associated with the given key, if it exists.
  ///
  /// The difference between `get` and `get_versioned` is that `get_versioned` will return the value even if the entry is removed.
  pub fn get_versioned(
    &self,
    version: Version,
    key: &[u8],
  ) -> Option<EntryRef<'_, Option<&[u8]>, C, A, RC>> {
    unsafe {
      let (n, eq) = self.find_near(version, key, false, true); // findLessOrEqual.

      let node = n?;
      let raw_node_key = node.get_key(&self.arena);
      let (value, _) = node.get_value_with_pointer(&self.arena);
      if eq {
        return Some(EntryRef::from_node_with_pointer(
          version,
          node,
          self,
          Some(raw_node_key),
          value,
        ));
      }

      if !self.cmp.equivalent(key, raw_node_key) {
        return None;
      }

      if node.version() > version {
        return None;
      }

      Some(EntryRef::from_node_with_pointer(
        version,
        node,
        self,
        Some(raw_node_key),
        value,
      ))
    }
  }

  /// Returns an `EntryRef` pointing to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  pub fn upper_bound(
    &self,
    version: Version,
    upper: Bound<&[u8]>,
  ) -> Option<EntryRef<'_, &[u8], C, A, RC>> {
    self.iter(version).seek_upper_bound(upper)
  }

  /// Returns an `EntryRef` pointing to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  pub fn lower_bound(
    &self,
    version: Version,
    lower: Bound<&[u8]>,
  ) -> Option<EntryRef<'_, &[u8], C, A, RC>> {
    self.iter(version).seek_lower_bound(lower)
  }
}

impl<A, RC, C> SkipList<A, RC, C>
where
  A: Allocator,
  RC: RefCounter,
{
  /// Returns a new iterator, this iterator will yield the latest version of all entries in the map less or equal to the given version.
  #[inline]
  pub fn iter(&self, version: Version) -> iterator::Iter<'_, &[u8], A, RC, C> {
    iterator::Iter::new(version, self, false)
  }

  /// Returns a new iterator, this iterator will yield all versions for all entries in the map less or equal to the given version.
  #[inline]
  pub fn iter_all_versions(&self, version: Version) -> iterator::Iter<'_, Option<&[u8]>, A, RC, C> {
    iterator::Iter::new(version, self, true)
  }

  /// Returns a iterator that within the range, this iterator will yield the latest version of all entries in the range less or equal to the given version.
  #[inline]
  pub fn range<Q, R>(&self, version: Version, range: R) -> iterator::Iter<'_, &[u8], A, RC, C, Q, R>
  where
    Q: ?Sized + Borrow<[u8]>,
    R: RangeBounds<Q>,
  {
    iterator::Iter::range(version, self, range, false)
  }

  /// Returns a iterator that within the range, this iterator will yield all versions for all entries in the range less or equal to the given version.
  #[inline]
  pub fn range_all_versions<Q, R>(
    &self,
    version: Version,
    range: R,
  ) -> iterator::Iter<'_, Option<&[u8]>, A, RC, C, Q, R>
  where
    Q: ?Sized + Borrow<[u8]>,
    R: RangeBounds<Q>,
  {
    iterator::Iter::range(version, self, range, true)
  }
}
