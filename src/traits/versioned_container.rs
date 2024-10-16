use core::ops::{Bound, RangeBounds};

use dbutils::{
  equivalent::Comparable,
  traits::{KeyRef, Type},
};

use super::{AllocatorSealed, Arena, EntryRef, Iter, VersionedEntryRef};
use crate::{allocator::WithVersion, iter::AllVersionsIter, Version};

/// A trait that provides versioned operations comparing to [`Container`](super::Container).
pub trait VersionedContainer<K, V>
where
  K: ?Sized + 'static,
  V: ?Sized + 'static,
  Self: Arena<K, V>,
  <Self::Allocator as AllocatorSealed>::Node: WithVersion,
{
  /// Returns the maximum version of all entries in the map.
  #[inline]
  fn max_version(&self) -> Version {
    self.as_ref().max_version()
  }

  /// Returns the minimum version of all entries in the map.
  #[inline]
  fn min_version(&self) -> Version {
    self.as_ref().min_version()
  }

  /// Returns `true` if the key exists in the map.
  ///
  /// This method will return `false` if the entry is marked as removed. If you want to check if the key exists even if it is marked as removed,
  /// you can use [`contains_key_versioned`](VersionedContainer::contains_key_versioned).
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{versioned::{sync::SkipMap, VersionedMap}, Options, VersionedContainer};
  ///
  /// let map = Options::new().with_capacity(1024).alloc::<str, str, SkipMap<_, _>>().unwrap();
  ///
  /// map.insert(0, "hello", "world").unwrap();
  ///
  /// map.get_or_remove(1, "hello").unwrap();
  ///
  /// assert!(!map.contains_key(1, "hello"));
  /// assert!(map.contains_key_versioned(1, "hello"));
  /// ```
  #[inline]
  fn contains_key<'a, Q>(&'a self, version: Version, key: &Q) -> bool
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
    Q: ?Sized + Comparable<K::Ref<'a>>,
  {
    self.as_ref().get(version, key).is_some()
  }

  /// Returns `true` if the key exists in the map, even if it is marked as removed.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{versioned::{sync::SkipMap, VersionedMap}, VersionedContainer, Options};
  ///
  /// let map = Options::new().with_capacity(1024).alloc::<str, str, SkipMap<_, _>>().unwrap();
  ///
  /// map.insert(0, "hello", "world").unwrap();
  ///
  /// map.get_or_remove(1, "hello").unwrap();
  ///
  /// assert!(!map.contains_key(1, "hello"));
  /// assert!(map.contains_key_versioned(1, "hello"));
  /// ```
  #[inline]
  fn contains_key_versioned<'a, Q>(&'a self, version: Version, key: &Q) -> bool
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
    Q: ?Sized + Comparable<K::Ref<'a>>,
  {
    self.as_ref().contains_key_versioned(version, key)
  }

  /// Returns the first entry in the map.
  #[inline]
  fn first<'a>(&'a self, version: Version) -> Option<EntryRef<'a, K, V, Self::Allocator>>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
  {
    self.as_ref().first(version)
  }

  /// Returns the last entry in the map.
  #[inline]
  fn last<'a>(&'a self, version: Version) -> Option<EntryRef<'a, K, V, Self::Allocator>>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
  {
    self.as_ref().last(version)
  }

  /// Returns the first entry in the map. The returned entry may not be in valid state. (i.e. the entry is removed)
  ///
  /// The difference between [`first`](VersionedContainer::first) and `first_versioned` is that `first_versioned` will return the value even if
  /// the entry is removed or not in a valid state.
  #[inline]
  fn first_versioned<'a>(
    &'a self,
    version: Version,
  ) -> Option<VersionedEntryRef<'a, K, V, Self::Allocator>>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
  {
    self.as_ref().first_versioned(version)
  }

  /// Returns the last entry in the map. The returned entry may not be in valid state. (i.e. the entry is removed)
  ///
  /// The difference between [`last`](VersionedContainer::last) and `last_versioned` is that `last_versioned` will return the value even if
  /// the entry is removed or not in a valid state.
  #[inline]
  fn last_versioned<'a>(
    &'a self,
    version: Version,
  ) -> Option<VersionedEntryRef<'a, K, V, Self::Allocator>>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
  {
    self.as_ref().last_versioned(version)
  }

  /// Returns the value associated with the given key, if it exists.
  ///
  /// This method will return `None` if the entry is marked as removed. If you want to get the entry even if it is marked as removed,
  /// you can use [`get_versioned`](VersionedContainer::get_versioned).
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{versioned::{sync::SkipMap, VersionedMap}, Options, VersionedContainer};
  ///
  /// let map = Options::new().with_capacity(1024).alloc::<str, str, SkipMap<_, _>>().unwrap();
  ///
  /// map.insert(0, "hello", "world").unwrap();
  ///
  /// let ent = map.get(0, "hello").unwrap();
  /// assert_eq!(ent.value(), "world");
  ///
  /// map.get_or_remove(1, "hello").unwrap();
  ///
  /// assert!(map.get(1, "hello").is_none());
  /// ```
  #[inline]
  fn get<'a, Q>(&'a self, version: Version, key: &Q) -> Option<EntryRef<'a, K, V, Self::Allocator>>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
    Q: ?Sized + Comparable<K::Ref<'a>>,
  {
    self.as_ref().get(version, key)
  }

  /// Returns the value associated with the given key, if it exists.
  ///
  /// The difference between `get` and `get_versioned` is that `get_versioned` will return the value even if the entry is removed.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{versioned::{sync::SkipMap, VersionedMap}, Options, VersionedContainer};
  ///
  /// let map = Options::new().with_capacity(1024).alloc::<str, str, SkipMap<_, _>>().unwrap();
  ///
  /// map.insert(0, "hello", "world").unwrap();
  ///
  /// map.get_or_remove(1, "hello").unwrap();
  ///
  /// assert!(map.get(1, "hello").is_none());
  ///
  /// let ent = map.get_versioned(1, "hello").unwrap();
  /// // value is None because the entry is marked as removed.
  /// assert!(ent.value().is_none());
  /// ```
  #[inline]
  fn get_versioned<'a, Q>(
    &'a self,
    version: Version,
    key: &Q,
  ) -> Option<VersionedEntryRef<'a, K, V, Self::Allocator>>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
    Q: ?Sized + Comparable<K::Ref<'a>>,
  {
    self.as_ref().get_versioned(version, key)
  }

  /// Returns an `EntryRef` pointing to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  #[inline]
  fn upper_bound<'a, Q>(
    &'a self,
    version: Version,
    upper: Bound<&Q>,
  ) -> Option<EntryRef<'a, K, V, Self::Allocator>>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
    Q: ?Sized + Comparable<K::Ref<'a>>,
  {
    self.as_ref().iter(version).seek_upper_bound(upper)
  }

  /// Returns an `EntryRef` pointing to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  #[inline]
  fn lower_bound<'a, Q>(
    &'a self,
    version: Version,
    lower: Bound<&Q>,
  ) -> Option<EntryRef<'a, K, V, Self::Allocator>>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
    Q: ?Sized + Comparable<K::Ref<'a>>,
  {
    self.as_ref().iter(version).seek_lower_bound(lower)
  }

  /// Returns an `VersionedEntryRef` pointing to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  ///
  /// The difference between [`upper_bound`](VersionedContainer::upper_bound) and `upper_bound_versioned` is that `upper_bound_versioned` will return the value even if the entry is removed.
  #[inline]
  fn upper_bound_versioned<'a, Q>(
    &'a self,
    version: Version,
    upper: Bound<&Q>,
  ) -> Option<VersionedEntryRef<'a, K, V, Self::Allocator>>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
    Q: ?Sized + Comparable<K::Ref<'a>>,
  {
    self
      .as_ref()
      .iter_all_versions(version)
      .seek_upper_bound(upper)
  }

  /// Returns an `VersionedEntryRef` pointing to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  ///
  /// The difference between [`lower_bound`](VersionedContainer::lower_bound) and `lower_bound_versioned` is that `lower_bound_versioned` will return the value even if the entry is removed.
  #[inline]
  fn lower_bound_versioned<'a, Q>(
    &'a self,
    version: Version,
    lower: Bound<&Q>,
  ) -> Option<VersionedEntryRef<'a, K, V, Self::Allocator>>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
    Q: ?Sized + Comparable<K::Ref<'a>>,
  {
    self
      .as_ref()
      .iter_all_versions(version)
      .seek_lower_bound(lower)
  }

  /// Returns a new iterator, this iterator will yield the latest version of all entries in the map less or equal to the given version.
  #[inline]
  fn iter<'a>(&'a self, version: Version) -> Iter<'a, K, V, Self::Allocator>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
  {
    self.as_ref().iter(version)
  }

  /// Returns a new iterator, this iterator will yield all versions for all entries in the map less or equal to the given version.
  #[inline]
  fn iter_all_versions<'a>(&'a self, version: Version) -> AllVersionsIter<'a, K, V, Self::Allocator>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
  {
    self.as_ref().iter_all_versions(version)
  }

  /// Returns a iterator that within the range, this iterator will yield the latest version of all entries in the range less or equal to the given version.
  #[inline]
  fn range<'a, Q, R>(&'a self, version: Version, range: R) -> Iter<'a, K, V, Self::Allocator, Q, R>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
    Q: ?Sized + Comparable<K::Ref<'a>>,
    R: RangeBounds<Q>,
  {
    self.as_ref().range(version, range)
  }

  /// Returns a iterator that within the range, this iterator will yield all versions for all entries in the range less or equal to the given version.
  #[inline]
  fn range_all_versions<'a, Q, R>(
    &'a self,
    version: Version,
    range: R,
  ) -> AllVersionsIter<'a, K, V, Self::Allocator, Q, R>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
    Q: ?Sized + Comparable<K::Ref<'a>>,
    R: RangeBounds<Q>,
  {
    self.as_ref().range_all_versions(version, range)
  }
}

impl<K, V, T> VersionedContainer<K, V> for T
where
  K: ?Sized + 'static,
  V: ?Sized + 'static,
  T: Arena<K, V>,
  <T::Allocator as AllocatorSealed>::Node: WithVersion,
{
}
