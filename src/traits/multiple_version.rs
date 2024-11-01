use core::ops::{Bound, RangeBounds};

use dbutils::{
  equivalent::Comparable,
  types::{KeyRef, MaybeStructured, Type},
};

use super::{AllocatorSealed, Arena, EntryRef, Iter, VersionedEntryRef};
use crate::{allocator::WithVersion, iter::AllVersionsIter, Version};

use super::*;

/// [`Map`] implementation for concurrent environment.
pub mod sync {
  pub use crate::sync::multiple_version::{
    AllVersionsIter, AllVersionsRange, Entry, Iter, Range, SkipMap, VersionedEntry,
  };
}

/// [`Map`] implementation for non-concurrent environment.
pub mod unsync {
  pub use crate::unsync::multiple_version::{
    AllVersionsIter, AllVersionsRange, Entry, Iter, Range, SkipMap, VersionedEntry,
  };
}

/// A fast, ARENA based `SkipMap` that supports multiple versions, forward and backward iteration.
///
/// - For concurrent environment, use [`sync::SkipMap`].
/// - For non-concurrent environment, use [`unsync::SkipMap`].
pub trait Map<K, V>
where
  K: ?Sized + 'static,
  V: ?Sized + 'static,
  Self: Arena<K, V>,
  <Self::Allocator as AllocatorSealed>::Node: WithVersion,
{
  /// Returns the maximum version of all entries in the map.
  #[inline]
  fn maximum_version(&self) -> Version {
    self.as_ref().maximum_version()
  }

  /// Returns the minimum version of all entries in the map.
  #[inline]
  fn minimum_version(&self) -> Version {
    self.as_ref().minimum_version()
  }

  /// Returns `true` if the map may contains an entry whose version is less than or equal to the given version.
  #[inline]
  fn may_contain_version(&self, v: Version) -> bool {
    self.as_ref().may_contain_version(v)
  }

  /// Returns `true` if the key exists in the map.
  ///
  /// This method will return `false` if the entry is marked as removed. If you want to check if the key exists even if it is marked as removed,
  /// you can use [`contains_key_versioned`](Map::contains_key_versioned).
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{multiple_version::{sync::SkipMap, Map}, Options};
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
    if !self.may_contain_version(version) {
      return false;
    }

    self.as_ref().get(version, key).is_some()
  }

  /// Returns `true` if the key exists in the map, even if it is marked as removed.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{multiple_version::{sync::SkipMap, Map}, Options};
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
    if !self.may_contain_version(version) {
      return false;
    }

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
    if !self.may_contain_version(version) {
      return None;
    }

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
    if !self.may_contain_version(version) {
      return None;
    }

    self.as_ref().last(version)
  }

  /// Returns the first entry in the map. The returned entry may not be in valid state. (i.e. the entry is removed)
  ///
  /// The difference between [`first`](Map::first) and `first_versioned` is that `first_versioned` will return the value even if
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
    if !self.may_contain_version(version) {
      return None;
    }

    self.as_ref().first_versioned(version)
  }

  /// Returns the last entry in the map. The returned entry may not be in valid state. (i.e. the entry is removed)
  ///
  /// The difference between [`last`](Map::last) and `last_versioned` is that `last_versioned` will return the value even if
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
    if !self.may_contain_version(version) {
      return None;
    }

    self.as_ref().last_versioned(version)
  }

  /// Returns the value associated with the given key, if it exists.
  ///
  /// This method will return `None` if the entry is marked as removed. If you want to get the entry even if it is marked as removed,
  /// you can use [`get_versioned`](Map::get_versioned).
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{multiple_version::{sync::SkipMap, Map}, Options};
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
    if !self.may_contain_version(version) {
      return None;
    }

    self.as_ref().get(version, key)
  }

  /// Returns the value associated with the given key, if it exists.
  ///
  /// The difference between `get` and `get_versioned` is that `get_versioned` will return the value even if the entry is removed.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{multiple_version::{sync::SkipMap, Map}, Options};
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
    if !self.may_contain_version(version) {
      return None;
    }

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
    if !self.may_contain_version(version) {
      return None;
    }

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
    if !self.may_contain_version(version) {
      return None;
    }

    self.as_ref().iter(version).seek_lower_bound(lower)
  }

  /// Returns an `VersionedEntryRef` pointing to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  ///
  /// The difference between [`upper_bound`](Map::upper_bound) and `upper_bound_versioned` is that `upper_bound_versioned` will return the value even if the entry is removed.
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
    if !self.may_contain_version(version) {
      return None;
    }

    self
      .as_ref()
      .iter_all_versions(version)
      .seek_upper_bound(upper)
  }

  /// Returns an `VersionedEntryRef` pointing to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  ///
  /// The difference between [`lower_bound`](Map::lower_bound) and `lower_bound_versioned` is that `lower_bound_versioned` will return the value even if the entry is removed.
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
    if !self.may_contain_version(version) {
      return None;
    }

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

  /// Upserts a new key-value pair if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert`](Map::get_or_insert), this method will update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  #[inline]
  fn insert<'a, 'b: 'a>(
    &'a self,
    version: Version,
    key: impl Into<MaybeStructured<'b, K>>,
    value: impl Into<MaybeStructured<'b, V>>,
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Among<K::Error, V::Error, Error>>
  where
    K: Type + 'b,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type + 'b,
  {
    self.as_ref().insert(version, key, value)
  }

  /// Upserts a new key-value pair at the given height if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert_at_height`](Map::get_or_insert_at_height), this method will update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{multiple_version::{sync::SkipMap, Map}, Options, Arena};
  ///
  /// let map = Options::new().with_capacity(1024).alloc::<str, str, SkipMap<_, _>>().unwrap();
  ///
  /// let height = map.random_height();
  /// map.insert_at_height(0, height, "hello", "world").unwrap();
  /// ```
  #[inline]
  fn insert_at_height<'a, 'b: 'a>(
    &'a self,
    version: Version,
    height: Height,
    key: impl Into<MaybeStructured<'b, K>>,
    value: impl Into<MaybeStructured<'b, V>>,
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Among<K::Error, V::Error, Error>>
  where
    K: Type + 'b,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type + 'b,
  {
    self.as_ref().insert_at_height(version, height, key, value)
  }

  /// Upserts a new key if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert_with_value_builder`](Map::get_or_insert_with_value_builder), this method will update the value if the key with the given version already exists.
  ///
  /// This method is useful when you want to insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// A placeholder will be inserted first, then you will get an [`VacantBuffer`],
  /// and you must fill the buffer with bytes later in the closure.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{multiple_version::{sync::SkipMap, Map}, ValueBuilder, Options};
  ///
  /// struct Person {
  ///   id: u32,
  ///   name: String,
  /// }
  ///
  /// impl Person {
  ///   fn encoded_size(&self) -> usize {
  ///     4 + self.name.len()
  ///   }
  /// }
  ///
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = Options::new().with_capacity(1024).alloc::<[u8], [u8], SkipMap<_, _>>().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size, |val: &mut skl::VacantBuffer<'_>| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// l.insert_with_value_builder::<core::convert::Infallible>(1, b"alice".as_slice(), vb)
  /// .unwrap();
  /// ```
  #[inline]
  fn insert_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    version: Version,
    key: impl Into<MaybeStructured<'b, K>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Among<K::Error, E, Error>>
  where
    K: Type + 'b,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type + 'b,
  {
    self.as_ref().insert_at_height_with_value_builder(
      version,
      self.random_height(),
      key,
      value_builder,
    )
  }

  /// Upserts a new key if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert_with_value_builder`](Map::get_or_insert_with_value_builder), this method will update the value if the key with the given version already exists.
  ///
  /// This method is useful when you want to insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// A placeholder will be inserted first, then you will get an [`VacantBuffer`],
  /// and you must fill the buffer with bytes later in the closure.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{multiple_version::{sync::SkipMap, Map}, ValueBuilder, Options, Arena};
  ///
  /// struct Person {
  ///   id: u32,
  ///   name: String,
  /// }
  ///
  /// impl Person {
  ///   fn encoded_size(&self) -> usize {
  ///     4 + self.name.len()
  ///   }
  /// }
  ///
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = Options::new().with_capacity(1024).alloc::<[u8], [u8], SkipMap<_, _>>().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size, |val: &mut skl::VacantBuffer<'_>| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.insert_at_height_with_value_builder::<core::convert::Infallible>(1, height, b"alice".as_slice(), vb)
  /// .unwrap();
  /// ```
  #[inline]
  fn insert_at_height_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    version: Version,
    height: Height,
    key: impl Into<MaybeStructured<'b, K>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Among<K::Error, E, Error>>
  where
    K: Type + 'b,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type + 'b,
  {
    self
      .as_ref()
      .insert_at_height_with_value_builder(version, height, key, value_builder)
  }

  /// Inserts a new key-value pair if it does not yet exist.
  ///
  /// Unlike [`insert`](Map::insert), this method will not update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully get_or_inserted.
  /// - Returns `Ok(Some(_))` if the key with the given version already exists.
  #[inline]
  fn get_or_insert<'a, 'b: 'a>(
    &'a self,
    version: Version,
    key: impl Into<MaybeStructured<'b, K>>,
    value: impl Into<MaybeStructured<'b, V>>,
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Among<K::Error, V::Error, Error>>
  where
    K: Type + 'b,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type + 'b,
  {
    self
      .as_ref()
      .get_or_insert_at_height(version, self.random_height(), key, value)
  }

  /// Inserts a new key-value pair at height if it does not yet exist.
  ///
  /// Unlike [`insert_at_height`](Map::insert_at_height), this method will not update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully get_or_inserted.
  /// - Returns `Ok(Some(_))` if the key with the given version already exists.
  #[inline]
  fn get_or_insert_at_height<'a, 'b: 'a>(
    &'a self,
    version: Version,
    height: Height,
    key: impl Into<MaybeStructured<'b, K>>,
    value: impl Into<MaybeStructured<'b, V>>,
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Among<K::Error, V::Error, Error>>
  where
    K: Type + 'b,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type + 'b,
  {
    self
      .as_ref()
      .get_or_insert_at_height(version, height, key, value)
  }

  /// Inserts a new key if it does not yet exist.
  ///
  /// Unlike [`insert_with_value_builder`](Map::insert_with_value_builder), this method will not update the value if the key with the given version already exists.
  ///
  /// This method is useful when you want to get_or_insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// A placeholder will be inserted first, then you will get an [`VacantBuffer`],
  /// and you must fill the buffer with bytes later in the closure.
  ///
  /// - Returns `Ok(None)` if the key was successfully get_or_inserted.
  /// - Returns `Ok(Some(_))` if the key with the given version already exists.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{multiple_version::{sync::SkipMap, Map}, ValueBuilder, Options};
  ///
  /// struct Person {
  ///   id: u32,
  ///   name: String,
  /// }
  ///
  /// impl Person {
  ///   fn encoded_size(&self) -> usize {
  ///     4 + self.name.len()
  ///   }
  /// }
  ///
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = Options::new().with_capacity(1024).alloc::<[u8], [u8], SkipMap<_, _>>().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size, |val: &mut skl::VacantBuffer<'_>| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  /// l.get_or_insert_with_value_builder::<core::convert::Infallible>(1, b"alice".as_slice(), vb)
  /// .unwrap();
  /// ```
  #[inline]
  fn get_or_insert_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    version: Version,
    key: impl Into<MaybeStructured<'b, K>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Among<K::Error, E, Error>>
  where
    K: Type + 'b,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type + 'b,
  {
    self.get_or_insert_at_height_with_value_builder(
      version,
      self.random_height(),
      key,
      value_builder,
    )
  }

  /// Inserts a new key if it does not yet exist.
  ///
  /// Unlike [`insert_at_height_with_value_builder`](Map::insert_at_height_with_value_builder), this method will not update the value if the key with the given version already exists.
  ///
  /// This method is useful when you want to get_or_insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// A placeholder will be inserted first, then you will get an [`VacantBuffer`],
  /// and you must fill the buffer with bytes later in the closure.
  ///
  /// - Returns `Ok(None)` if the key was successfully get_or_inserted.
  /// - Returns `Ok(Some(_))` if the key with the given version already exists.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{multiple_version::{sync::SkipMap, Map}, ValueBuilder, Options, Arena};
  ///
  /// struct Person {
  ///   id: u32,
  ///   name: String,
  /// }
  ///
  /// impl Person {
  ///   fn encoded_size(&self) -> usize {
  ///     4 + self.name.len()
  ///   }
  /// }
  ///
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = Options::new().with_capacity(1024).alloc::<[u8], [u8], SkipMap<_, _>>().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size, |val: &mut skl::VacantBuffer<'_>| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.get_or_insert_at_height_with_value_builder::<core::convert::Infallible>(1, height, b"alice".as_slice(), vb)
  /// .unwrap();
  /// ```
  #[inline]
  fn get_or_insert_at_height_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    version: Version,
    height: Height,
    key: impl Into<MaybeStructured<'b, K>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Among<K::Error, E, Error>>
  where
    K: Type + 'b,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type + 'b,
  {
    self
      .as_ref()
      .get_or_insert_at_height_with_value_builder(version, height, key, value_builder)
  }

  /// Upserts a new key if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert_with_builders`](Map::get_or_insert_with_builders), this method will update the value if the key with the given version already exists.
  ///
  /// This method is useful when you want to insert a key and you know the key size and value size but you do not have the key and value
  /// at this moment.
  ///
  /// A placeholder will be inserted first, then you will get an [`VacantBuffer`],
  /// and you must fill the buffer with bytes later in the closure.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{multiple_version::{sync::SkipMap, Map}, KeyBuilder, ValueBuilder, Options};
  ///
  /// struct Person {
  ///   id: u32,
  ///   name: String,
  /// }
  ///
  /// impl Person {
  ///   fn encoded_size(&self) -> usize {
  ///     4 + self.name.len()
  ///   }
  /// }
  ///
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = Options::new().with_capacity(1024).alloc::<[u8], [u8], SkipMap<_, _>>().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |key: &mut skl::VacantBuffer<'_>| {
  ///   key.put_slice(b"alice").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size, |val: &mut skl::VacantBuffer<'_>| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// l.insert_with_builders::<(), ()>(1, kb, vb)
  /// .unwrap();
  /// ```
  #[inline]
  fn insert_with_builders<'a, KE, VE>(
    &'a self,
    version: Version,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Among<KE, VE, Error>>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
  {
    self.as_ref().insert_at_height_with_builders(
      version,
      self.random_height(),
      key_builder,
      value_builder,
    )
  }

  /// Upserts a new key if it does not yet exist, if the key with the given version already exists, it will update the value.
  ///
  /// Unlike [`get_or_insert_with_builders`](Map::get_or_insert_with_builders), this method will update the value if the key with the given version already exists.
  ///
  /// This method is useful when you want to insert a key and you know the key size and value size but you do not have the key and value
  /// at this moment.
  ///
  /// A placeholder will be inserted first, then you will get an [`VacantBuffer`],
  /// and you must fill the buffer with bytes later in the closure.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{multiple_version::{sync::SkipMap, Map}, KeyBuilder, ValueBuilder, Options, Arena};
  ///
  /// struct Person {
  ///   id: u32,
  ///   name: String,
  /// }
  ///
  /// impl Person {
  ///   fn encoded_size(&self) -> usize {
  ///     4 + self.name.len()
  ///   }
  /// }
  ///
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = Options::new().with_capacity(1024).alloc::<[u8], [u8], SkipMap<_, _>>().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |key: &mut skl::VacantBuffer<'_>| {
  ///   key.put_slice(b"alice").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size, |val: &mut skl::VacantBuffer<'_>| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.insert_at_height_with_builders::<(), ()>(1, height, kb, vb)
  /// .unwrap();
  /// ```
  #[inline]
  fn insert_at_height_with_builders<'a, KE, VE>(
    &'a self,
    version: Version,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Among<KE, VE, Error>>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
  {
    self
      .as_ref()
      .insert_at_height_with_builders(version, height, key_builder, value_builder)
  }

  /// Inserts a new key if it does not yet exist.
  ///
  /// Unlike [`insert_with_builders`](Map::insert_with_builders), this method will not update the value if the key with the given version already exists.
  ///
  /// This method is useful when you want to get_or_insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// A placeholder will be inserted first, then you will get an [`VacantBuffer`],
  /// and you must fill the buffer with bytes later in the closure.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{multiple_version::{sync::SkipMap, Map}, KeyBuilder, ValueBuilder, Options};
  ///
  /// struct Person {
  ///   id: u32,
  ///   name: String,
  /// }
  ///
  /// impl Person {
  ///   fn encoded_size(&self) -> usize {
  ///     4 + self.name.len()
  ///   }
  /// }
  ///
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = Options::new().with_capacity(1024).alloc::<[u8], [u8], SkipMap<_, _>>().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |key: &mut skl::VacantBuffer<'_>| {
  ///   key.put_slice(b"alice").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size, |val: &mut skl::VacantBuffer<'_>| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// l.get_or_insert_with_builders::<(), ()>(1, kb, vb)
  /// .unwrap();
  /// ```
  #[inline]
  fn get_or_insert_with_builders<'a, KE, VE>(
    &'a self,
    version: Version,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Among<KE, VE, Error>>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
  {
    self.as_ref().get_or_insert_at_height_with_builders(
      version,
      self.random_height(),
      key_builder,
      value_builder,
    )
  }

  /// Inserts a new key if it does not yet exist.
  ///
  /// Unlike [`insert_at_height_with_builders`](Map::insert_at_height_with_builders), this method will not update the value if the key with the given version already exists.
  ///
  /// This method is useful when you want to get_or_insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// A placeholder will be inserted first, then you will get an [`VacantBuffer`],
  /// and you must fill the buffer with bytes later in the closure.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{multiple_version::{sync::SkipMap, Map}, KeyBuilder, ValueBuilder, Options, Arena};
  ///
  /// struct Person {
  ///   id: u32,
  ///   name: String,
  /// }
  ///
  /// impl Person {
  ///   fn encoded_size(&self) -> usize {
  ///     4 + self.name.len()
  ///   }
  /// }
  ///
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = Options::new().with_capacity(1024).alloc::<[u8], [u8], SkipMap<_, _>>().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |key: &mut skl::VacantBuffer<'_>| {
  ///   key.put_slice(b"alice").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size, |val: &mut skl::VacantBuffer<'_>| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.get_or_insert_at_height_with_builders::<(), ()>(1, height, kb, vb)
  /// .unwrap();
  /// ```
  #[inline]
  fn get_or_insert_at_height_with_builders<'a, KE, VE>(
    &'a self,
    version: Version,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Among<KE, VE, Error>>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
  {
    self
      .as_ref()
      .get_or_insert_at_height_with_builders(version, height, key_builder, value_builder)
  }

  /// Removes the key-value pair if it exists. A CAS operation will be used to ensure the operation is atomic.
  ///
  /// Unlike [`get_or_remove`](Map::get_or_remove), this method will remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)`:
  ///   - if the remove operation is successful or the key is marked in remove status by other threads.
  /// - Returns `Ok(Either::Right(current))` if the key with the given version already exists
  ///   and the entry is not successfully removed because of an update on this entry happens in another thread.
  #[inline]
  fn compare_remove<'a, 'b: 'a>(
    &'a self,
    version: Version,
    key: impl Into<MaybeStructured<'b, K>>,
    success: Ordering,
    failure: Ordering,
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Either<K::Error, Error>>
  where
    K: Type + 'b,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
  {
    self.compare_remove_at_height(version, self.random_height(), key, success, failure)
  }

  /// Removes the key-value pair if it exists. A CAS operation will be used to ensure the operation is atomic.
  ///
  /// Unlike [`get_or_remove_at_height`](Map::get_or_remove_at_height), this method will remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)`:
  ///   - if the remove operation is successful or the key is marked in remove status by other threads.
  /// - Returns `Ok(Either::Right(current))` if the key with the given version already exists
  ///   and the entry is not successfully removed because of an update on this entry happens in another thread.
  #[inline]
  fn compare_remove_at_height<'a, 'b: 'a>(
    &'a self,
    version: Version,
    height: Height,
    key: impl Into<MaybeStructured<'b, K>>,
    success: Ordering,
    failure: Ordering,
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Either<K::Error, Error>>
  where
    K: Type + 'b,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
  {
    self
      .as_ref()
      .compare_remove_at_height(version, height, key, success, failure)
  }

  /// Gets or removes the key-value pair if it exists.
  ///
  /// Unlike [`compare_remove`](Map::compare_remove), this method will not remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key does not exist.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists.
  #[inline]
  fn get_or_remove<'a, 'b: 'a>(
    &'a self,
    version: Version,
    key: impl Into<MaybeStructured<'b, K>>,
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Either<K::Error, Error>>
  where
    K: Type + 'b,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
  {
    self.get_or_remove_at_height(version, self.random_height(), key)
  }

  /// Gets or removes the key-value pair if it exists.
  ///
  /// Unlike [`compare_remove_at_height`](Map::compare_remove_at_height), this method will not remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key does not exist.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{multiple_version::{sync::SkipMap, Map}, Options, Arena};
  ///
  /// let map = Options::new().with_capacity(1024).alloc::<str, str, SkipMap<_, _>>().unwrap();
  ///
  /// map.insert(0, "hello", "world").unwrap();
  ///
  /// let height = map.random_height();
  /// map.get_or_remove_at_height(0, height, "hello").unwrap();
  /// ```
  #[inline]
  fn get_or_remove_at_height<'a, 'b: 'a>(
    &'a self,
    version: Version,
    height: Height,
    key: impl Into<MaybeStructured<'b, K>>,
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Either<K::Error, Error>>
  where
    K: Type + 'b,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
  {
    self.as_ref().get_or_remove_at_height(version, height, key)
  }

  /// Gets or removes the key-value pair if it exists.
  ///
  /// - Returns `Ok(None)` if the key does not exist.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists.
  ///
  /// This method is useful when you want to get_or_remove a key and you know the key size but you do not have the key
  /// at this moment.
  ///
  /// A placeholder will be inserted first, then you will get an [`VacantBuffer`],
  /// and you must fill the buffer with bytes later in the closure.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{multiple_version::{sync::SkipMap, Map}, KeyBuilder, Options};
  ///
  /// struct Person {
  ///   id: u32,
  ///   name: String,
  /// }
  ///
  /// impl Person {
  ///   fn encoded_size(&self) -> usize {
  ///     4 + self.name.len()
  ///   }
  /// }
  ///
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = Options::new().with_capacity(1024).alloc::<[u8], [u8], SkipMap<_, _>>().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |key: &mut skl::VacantBuffer<'_>| {
  ///   key.put_slice(b"alice").unwrap();
  ///   Ok(())
  /// });
  /// l.get_or_remove_with_builder::<core::convert::Infallible>(1, kb)
  /// .unwrap();
  /// ```
  #[inline]
  fn get_or_remove_with_builder<'a, 'b: 'a, E>(
    &'a self,
    version: Version,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Either<E, Error>>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
  {
    self
      .as_ref()
      .get_or_remove_at_height_with_builder(version, self.random_height(), key_builder)
  }

  /// Gets or removes the key-value pair if it exists.
  ///
  /// - Returns `Ok(None)` if the key does not exist.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists.
  ///
  /// This method is useful when you want to get_or_remove a key and you know the key size but you do not have the key
  /// at this moment.
  ///
  /// A placeholder will be inserted first, then you will get an [`VacantBuffer`],
  /// and you must fill the buffer with bytes later in the closure.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{multiple_version::{sync::SkipMap, Map}, KeyBuilder, Options, Arena};
  ///
  /// struct Person {
  ///   id: u32,
  ///   name: String,
  /// }
  ///
  /// impl Person {
  ///   fn encoded_size(&self) -> usize {
  ///     4 + self.name.len()
  ///   }
  /// }
  ///
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = Options::new().with_capacity(1024).alloc::<[u8], [u8], SkipMap<_, _>>().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |key: &mut skl::VacantBuffer<'_>| {
  ///   key.put_slice(b"alice").unwrap();
  ///   Ok(())
  /// });
  /// let height = l.random_height();
  /// l.get_or_remove_at_height_with_builder::<core::convert::Infallible>(1, height, kb)
  /// .unwrap();
  /// ```
  #[inline]
  fn get_or_remove_at_height_with_builder<'a, 'b: 'a, E>(
    &'a self,
    version: Version,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Either<E, Error>>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
  {
    self
      .as_ref()
      .get_or_remove_at_height_with_builder(version, height, key_builder)
  }
}

impl<K, V, T> Map<K, V> for T
where
  K: ?Sized + 'static,
  V: ?Sized + 'static,
  T: Arena<K, V>,
  <T::Allocator as AllocatorSealed>::Node: WithVersion,
{
}
