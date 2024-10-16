use core::{
  mem,
  ops::{Bound, RangeBounds},
  ptr::NonNull,
  sync::atomic::Ordering,
};
use std::boxed::Box;

use dbutils::{
  buffer::VacantBuffer,
  equivalent::{Comparable, Equivalent},
  traits::{KeyRef, Type},
};
use rarena_allocator::Allocator as _;

use crate::{
  allocator::{Allocator, Header, Link, Node, NodePointer},
  random_height, ty_ref, Error, Height, ValueBuilder, Version,
};

use super::{iterator, EntryRef, SkipList, VersionedEntryRef};

mod update;

type RemoveValueBuilder<E> =
  ValueBuilder<std::boxed::Box<dyn Fn(&mut VacantBuffer<'_>) -> Result<(), E>>>;

impl<K: ?Sized, V: ?Sized, A: Allocator> SkipList<K, V, A> {
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

  /// Returns the offset of the data section in the `SkipList`.
  ///
  /// By default, `SkipList` will allocate meta, head node, and tail node in the ARENA,
  /// and the data section will be allocated after the tail node.
  ///
  /// This method will return the offset of the data section in the ARENA.
  #[inline]
  pub const fn data_offset(&self) -> usize {
    self.data_offset as usize
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

  /// Returns the number of remaining bytes can be allocated by the arena.
  #[inline]
  pub fn remaining(&self) -> usize {
    self.arena.remaining()
  }

  /// Returns how many bytes are discarded by the ARENA.
  #[inline]
  pub fn discarded(&self) -> u32 {
    self.arena.discarded()
  }

  /// Returns the number of bytes that have allocated from the arena.
  #[inline]
  pub fn allocated(&self) -> usize {
    self.arena.allocated()
  }

  /// Returns the capacity of the arena.
  #[inline]
  pub fn capacity(&self) -> usize {
    self.arena.capacity()
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
  pub fn max_version(&self) -> u64 {
    self.meta().max_version()
  }

  /// Returns the minimum version of all entries in the map.
  #[inline]
  pub fn min_version(&self) -> u64 {
    self.meta().min_version()
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
      + mem::align_of::<A::Trailer>() - 1 // max trailer padding
      + mem::size_of::<A::Trailer>()
      + value_size
  }

  /// Clear the skiplist to empty and re-initialize.
  ///
  /// ## Safety
  /// - The current pointers get from the ARENA cannot be used anymore after calling this method.
  /// - This method is not thread-safe.
  pub unsafe fn clear(&mut self) -> Result<(), Error> {
    self.arena.clear()?;

    let options = self.arena.options();

    if self.arena.unify() {
      self.meta = self
        .arena
        .allocate_header(self.meta.as_ref().magic_version())?;
    } else {
      let magic_version = self.meta.as_ref().magic_version();
      let _ = Box::from_raw(self.meta.as_ptr());
      self.meta = NonNull::new_unchecked(Box::into_raw(Box::new(<A::Header as Header>::new(
        magic_version,
      ))));
    }

    let max_height: u8 = options.max_height().into();
    let head = self.arena.allocate_full_node(max_height)?;
    let tail = self.arena.allocate_full_node(max_height)?;

    // Safety:
    // We will always allocate enough space for the head node and the tail node.
    unsafe {
      // Link all head/tail levels together.
      for i in 0..(max_height as usize) {
        let head_link = head.tower(&self.arena, i);
        let tail_link = tail.tower(&self.arena, i);
        head_link.store_next_offset(tail.offset(), Ordering::Relaxed);
        tail_link.store_prev_offset(head.offset(), Ordering::Relaxed);
      }
    }

    self.head = head;
    self.tail = tail;
    Ok(())
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

impl<K, V, A: Allocator> SkipList<K, V, A>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
  A: Allocator,
{
  /// Returns `true` if the key exists in the map.
  ///
  /// This method will return `false` if the entry is marked as removed. If you want to check if the key exists even if it is marked as removed,
  /// you can use [`contains_key_versioned`](SkipList::contains_key_versioned).
  #[inline]
  pub fn contains_key<'a, Q>(&'a self, version: Version, key: &Q) -> bool
  where
    Q: ?Sized + Comparable<K::Ref<'a>>,
  {
    self.get(version, key).is_some()
  }

  /// Returns `true` if the key exists in the map, even if it is marked as removed.
  #[inline]
  pub fn contains_key_versioned<'a, Q>(&'a self, version: Version, key: &Q) -> bool
  where
    Q: ?Sized + Comparable<K::Ref<'a>>,
  {
    self.get_versioned(version, key).is_some()
  }

  /// Returns the first entry in the map.
  pub fn first<'a>(&'a self, version: Version) -> Option<EntryRef<'a, K, V, A>>
  where
    K::Ref<'a>: KeyRef<'a, K>,
  {
    self.iter(version).next()
  }

  /// Returns the last entry in the map.
  pub fn last<'a>(&'a self, version: Version) -> Option<EntryRef<'a, K, V, A>>
  where
    K::Ref<'a>: KeyRef<'a, K>,
  {
    self.iter(version).last()
  }

  /// Returns the first entry in the map.
  pub fn first_versioned<'a>(&'a self, version: Version) -> Option<VersionedEntryRef<'a, K, V, A>>
  where
    K::Ref<'a>: KeyRef<'a, K>,
  {
    self.iter_all_versions(version).next()
  }

  /// Returns the last entry in the map.
  pub fn last_versioned<'a>(&'a self, version: Version) -> Option<VersionedEntryRef<'a, K, V, A>>
  where
    K::Ref<'a>: KeyRef<'a, K>,
  {
    self.iter_all_versions(version).last()
  }

  /// Returns the value associated with the given key, if it exists.
  ///
  /// This method will return `None` if the entry is marked as removed. If you want to get the entry even if it is marked as removed,
  /// you can use [`get_versioned`](SkipList::get_versioned).
  pub fn get<'a, Q>(&'a self, version: Version, key: &Q) -> Option<EntryRef<'a, K, V, A>>
  where
    Q: ?Sized + Comparable<K::Ref<'a>>,
  {
    unsafe {
      let (n, eq) = self.find_near(version, key, false, true, true); // findLessOrEqual.

      let node = n?;
      let node_key = node.get_key(&self.arena);
      let (value, pointer) = node.get_value_and_trailer_with_pointer(&self.arena);
      if eq {
        return value.map(|_| {
          EntryRef(VersionedEntryRef::from_node_with_pointer(
            version,
            node,
            self,
            pointer,
            Some(node_key),
            None,
          ))
        });
      }

      if !Equivalent::equivalent(key, &ty_ref::<K>(node_key)) {
        return None;
      }

      if node.version() > version {
        return None;
      }

      value.map(|_| {
        EntryRef(VersionedEntryRef::from_node_with_pointer(
          version,
          node,
          self,
          pointer,
          Some(node_key),
          None,
        ))
      })
    }
  }

  /// Returns the value associated with the given key, if it exists.
  ///
  /// The difference between `get` and `get_versioned` is that `get_versioned` will return the value even if the entry is removed.
  pub fn get_versioned<'a, Q>(
    &'a self,
    version: Version,
    key: &Q,
  ) -> Option<VersionedEntryRef<'a, K, V, A>>
  where
    Q: ?Sized + Comparable<K::Ref<'a>>,
  {
    unsafe {
      let (n, eq) = self.find_near(version, key, false, true, false); // findLessOrEqual.

      let node = n?;
      let node_key = node.get_key(&self.arena);
      let (_, pointer) = node.get_value_and_trailer_with_pointer(&self.arena);
      if eq {
        return Some(VersionedEntryRef::from_node_with_pointer(
          version,
          node,
          self,
          pointer,
          Some(node_key),
          None,
        ));
      }

      if !Equivalent::equivalent(key, &ty_ref::<K>(node_key)) {
        return None;
      }

      if node.version() > version {
        return None;
      }

      Some(VersionedEntryRef::from_node_with_pointer(
        version,
        node,
        self,
        pointer,
        Some(node_key),
        None,
      ))
    }
  }

  /// Returns an `EntryRef` pointing to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  pub fn upper_bound<'a, Q>(
    &'a self,
    version: Version,
    upper: Bound<&Q>,
  ) -> Option<EntryRef<'a, K, V, A>>
  where
    K::Ref<'a>: KeyRef<'a, K>,
    Q: ?Sized + Comparable<K::Ref<'a>>,
  {
    self.iter(version).seek_upper_bound(upper)
  }

  /// Returns an `EntryRef` pointing to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  pub fn lower_bound<'a, Q>(
    &'a self,
    version: Version,
    lower: Bound<&Q>,
  ) -> Option<EntryRef<'a, K, V, A>>
  where
    K::Ref<'a>: KeyRef<'a, K>,
    Q: ?Sized + Comparable<K::Ref<'a>>,
  {
    self.iter(version).seek_lower_bound(lower)
  }

  /// Returns a new iterator, this iterator will yield the latest version of all entries in the map less or equal to the given version.
  #[inline]
  pub fn iter<'a>(&'a self, version: Version) -> iterator::Iter<'a, K, V, A>
  where
    K::Ref<'a>: KeyRef<'a, K>,
  {
    iterator::Iter::new(version, self)
  }

  /// Returns a new iterator, this iterator will yield all versions for all entries in the map less or equal to the given version.
  #[inline]
  pub fn iter_all_versions<'a>(&'a self, version: Version) -> iterator::AllVersionsIter<'a, K, V, A>
  where
    K::Ref<'a>: KeyRef<'a, K>,
  {
    iterator::AllVersionsIter::new(version, self, true)
  }

  /// Returns a iterator that within the range, this iterator will yield the latest version of all entries in the range less or equal to the given version.
  #[inline]
  pub fn range<'a, Q, R>(&'a self, version: Version, range: R) -> iterator::Iter<'a, K, V, A, Q, R>
  where
    K::Ref<'a>: KeyRef<'a, K>,
    Q: ?Sized + Comparable<K::Ref<'a>>,
    R: RangeBounds<Q>,
  {
    iterator::Iter::range(version, self, range)
  }

  /// Returns a iterator that within the range, this iterator will yield all versions for all entries in the range less or equal to the given version.
  #[inline]
  pub fn range_all_versions<'a, Q, R>(
    &'a self,
    version: Version,
    range: R,
  ) -> iterator::AllVersionsIter<'a, K, V, A, Q, R>
  where
    K::Ref<'a>: KeyRef<'a, K>,
    Q: ?Sized + Comparable<K::Ref<'a>>,
    R: RangeBounds<Q>,
  {
    iterator::AllVersionsIter::range(version, self, range, true)
  }
}
