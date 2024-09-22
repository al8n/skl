use core::{
  borrow::Borrow,
  ops::{Bound, RangeBounds},
};

use dbutils::Comparator;

use super::{AllocatorSealed, Arena, EntryRef, Iter};
use crate::{allocator::WithVersion, AllVersionsIter, Version, VersionedEntryRef};

/// a
pub trait VersionedContainer
where
  Self: Arena,
  Self::Comparator: Comparator,
  <Self::Allocator as AllocatorSealed>::Node: WithVersion,
{
  /// Returns `true` if the key exists in the map.
  ///
  /// This method will return `false` if the entry is marked as removed. If you want to check if the key exists even if it is marked as removed,
  /// you can use [`contains_key_versioned`](SkipMap::contains_key_versioned).
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{sync::full::SkipMap, Options};
  ///
  /// let map = SkipMap::new(Options::new()).unwrap();
  ///
  /// map.insert(0, b"hello", b"world", ()).unwrap();
  ///
  /// map.get_or_remove(1, b"hello", ()).unwrap();
  ///
  /// assert!(!map.contains_key(1, b"hello"));
  /// assert!(map.contains_key_versioned(1, b"hello"));
  /// ```
  #[inline]
  fn contains_key(&self, version: Version, key: &[u8]) -> bool {
    self.get(version, key).is_some()
  }

  /// Returns `true` if the key exists in the map, even if it is marked as removed.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{sync::full::SkipMap, Options};
  ///
  /// let map = SkipMap::new(Options::new()).unwrap();
  ///
  /// map.insert(0, b"hello", b"world", ()).unwrap();
  ///
  /// map.get_or_remove(1, b"hello", ()).unwrap();
  ///
  /// assert!(!map.contains_key(1, b"hello"));
  /// assert!(map.contains_key_versioned(1, b"hello"));
  /// ```
  #[inline]
  fn contains_key_versioned(&self, version: Version, key: &[u8]) -> bool {
    self.as_ref().contains_key_versioned(version, key)
  }

  /// Returns the first entry in the map.
  #[inline]
  fn first(&self, version: Version) -> Option<EntryRef<'_, Self::Allocator>> {
    self.iter(version).seek_lower_bound(Bound::Unbounded)
  }

  /// Returns the last entry in the map.
  #[inline]
  fn last(&self, version: Version) -> Option<EntryRef<'_, Self::Allocator>> {
    self.iter(version).seek_upper_bound(Bound::Unbounded)
  }

  /// Returns the value associated with the given key, if it exists.
  ///
  /// This method will return `None` if the entry is marked as removed. If you want to get the entry even if it is marked as removed,
  /// you can use [`get_versioned`](SkipMap::get_versioned).
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{sync::full::SkipMap, Options};
  ///
  /// let map = SkipMap::new(Options::new()).unwrap();
  ///
  /// map.insert(0, b"hello", b"world", ()).unwrap();
  ///
  /// let ent = map.get(0, b"hello").unwrap();
  /// assert_eq!(ent.value(), b"world");
  ///
  /// map.get_or_remove(1, b"hello", ()).unwrap();
  ///
  /// assert!(map.get(1, b"hello").is_none());
  /// ```
  #[inline]
  fn get(&self, version: Version, key: &[u8]) -> Option<EntryRef<'_, Self::Allocator>> {
    self.as_ref().get(version, key)
  }

  /// Returns the value associated with the given key, if it exists.
  ///
  /// The difference between `get` and `get_versioned` is that `get_versioned` will return the value even if the entry is removed.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{sync::full::SkipMap, Options};
  ///
  /// let map = SkipMap::new(Options::new()).unwrap();
  ///
  /// map.insert(0, b"hello", b"world", ()).unwrap();
  ///
  /// map.get_or_remove(1, b"hello", ()).unwrap();
  ///
  /// assert!(map.get(1, b"hello").is_none());
  ///
  /// let ent = map.get_versioned(1, b"hello").unwrap();
  /// // value is None because the entry is marked as removed.
  /// assert!(ent.value().is_none());
  /// ```
  #[inline]
  fn get_versioned(
    &self,
    version: Version,
    key: &[u8],
  ) -> Option<VersionedEntryRef<'_, Self::Allocator>> {
    self.as_ref().get_versioned(version, key)
  }

  /// Returns an `EntryRef` pointing to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  #[inline]
  fn upper_bound(
    &self,
    version: Version,
    upper: Bound<&[u8]>,
  ) -> Option<EntryRef<'_, Self::Allocator>> {
    self.iter(version).seek_upper_bound(upper)
  }

  /// Returns an `EntryRef` pointing to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  #[inline]
  fn lower_bound(
    &self,
    version: Version,
    lower: Bound<&[u8]>,
  ) -> Option<EntryRef<'_, Self::Allocator>> {
    self.iter(version).seek_lower_bound(lower)
  }

  /// Returns a new iterator, this iterator will yield the latest version of all entries in the map less or equal to the given version.
  #[inline]
  fn iter(&self, version: Version) -> Iter<'_, Self::Allocator, Self::Comparator> {
    self.as_ref().iter(version)
  }

  /// Returns a new iterator, this iterator will yield all versions for all entries in the map less or equal to the given version.
  #[inline]
  fn iter_all_versions(
    &self,
    version: Version,
  ) -> AllVersionsIter<'_, Self::Allocator, Self::Comparator> {
    self.as_ref().iter_all_versions(version)
  }

  /// Returns a iterator that within the range, this iterator will yield the latest version of all entries in the range less or equal to the given version.
  #[inline]
  fn range<'a, Q, R>(
    &'a self,
    version: Version,
    range: R,
  ) -> Iter<'a, Self::Allocator, Self::Comparator, Q, R>
  where
    Q: ?Sized + Borrow<[u8]>,
    R: RangeBounds<Q> + 'a,
  {
    self.as_ref().range(version, range)
  }

  /// Returns a iterator that within the range, this iterator will yield all versions for all entries in the range less or equal to the given version.
  #[inline]
  fn range_all_versions<'a, Q, R>(
    &'a self,
    version: Version,
    range: R,
  ) -> AllVersionsIter<'a, Self::Allocator, Self::Comparator, Q, R>
  where
    Q: ?Sized + Borrow<[u8]>,
    R: RangeBounds<Q> + 'a,
  {
    self.as_ref().range_all_versions(version, range)
  }
}

impl<T> VersionedContainer for T
where
  T: Arena,
  T::Comparator: Comparator,
  <T::Allocator as AllocatorSealed>::Node: WithVersion,
{
}
