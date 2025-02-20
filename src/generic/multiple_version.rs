use core::{
  ops::{Bound, RangeBounds},
  sync::atomic::Ordering,
};

use among::Among;
use dbutils::{
  buffer::VacantBuffer,
  equivalentor::{TypeRefComparator, TypeRefQueryComparator},
  types::{MaybeStructured, Type},
};
use either::Either;

use crate::{
  allocator::{Allocator, Sealed, WithVersion},
  error::Error,
  generic::{Active, MaybeTombstone},
  ref_counter::RefCounter,
  Arena, Header, Height, KeyBuilder, ValueBuilder, Version,
};

use super::{
  list::{
    iterator::{Iter, Range},
    EntryRef,
  },
  Ascend,
};

/// Implementations for single-threaded environments.
pub mod unsync {
  use crate::generic::Ascend;
  pub use crate::unsync::{multiple_version::Allocator, RefCounter};

  #[cfg(any(all(test, not(miri)), all_skl_tests, test_generic_unsync_versioned,))]
  mod tests {
    crate::__generic_multiple_version_map_tests!("unsync_multiple_version_map": super::SkipMap<[u8], [u8]>);
  }

  type SkipList<K, V, C = Ascend> = super::super::list::SkipList<K, V, C, Allocator, RefCounter>;

  /// Iterator over the [`SkipMap`].
  pub type Iter<'a, K, V, S, C = Ascend> =
    super::super::iter::Iter<'a, K, V, S, C, Allocator, RefCounter>;

  /// Iterator over a subset of the [`SkipMap`].
  pub type Range<'a, K, V, S, Q, R, C = Ascend> =
    super::super::iter::Range<'a, K, V, S, C, Allocator, RefCounter, Q, R>;

  /// The entry reference of the [`SkipMap`].
  pub type Entry<'a, K, V, S, C = Ascend> =
    super::super::entry::EntryRef<'a, K, V, S, C, Allocator, RefCounter>;

  /// A fast, ARENA based `SkipMap` that supports multiple versions, forward and backward iteration.
  ///
  /// If you want to use in concurrent environment, you can use [`multiple_version::sync::SkipMap`](crate::generic::multiple_version::sync::SkipMap).
  #[repr(transparent)]
  pub struct SkipMap<K: ?Sized, V: ?Sized, C = Ascend>(SkipList<K, V, C>);

  impl<K: ?Sized, V: ?Sized, C: Clone> Clone for SkipMap<K, V, C> {
    #[inline]
    fn clone(&self) -> Self {
      Self(self.0.clone())
    }
  }

  impl<K: ?Sized, V: ?Sized, C> From<SkipList<K, V, C>> for SkipMap<K, V, C> {
    #[inline]
    fn from(list: SkipList<K, V, C>) -> Self {
      Self(list)
    }
  }

  impl<K: ?Sized + 'static, V: ?Sized + 'static, C> crate::traits::List for SkipMap<K, V, C> {
    type Constructable = SkipList<K, V, C>;

    #[inline]
    fn as_ref(&self) -> &Self::Constructable {
      &self.0
    }

    #[inline]
    fn as_mut(&mut self) -> &mut Self::Constructable {
      &mut self.0
    }

    #[inline]
    fn meta(
      &self,
    ) -> &<<Self::Constructable as crate::traits::Constructable>::Allocator as super::Sealed>::Meta
    {
      self.0.meta()
    }
  }

  impl<K, V, C> super::Map<K, V, C> for SkipMap<K, V, C>
  where
    K: ?Sized + 'static,
    V: ?Sized + 'static,
    C: 'static,
  {
    type Allocator = Allocator;
    type RefCounter = RefCounter;
  }
}

/// Implementations for concurrent environments.
pub mod sync {
  use crate::generic::Ascend;
  pub use crate::sync::{multiple_version::Allocator, RefCounter};

  #[cfg(any(all(test, not(miri)), all_skl_tests, test_generic_sync_versioned,))]
  mod tests {
    crate::__generic_multiple_version_map_tests!("sync_multiple_version_map": super::SkipMap<[u8], [u8]>);
  }

  #[cfg(any(
    all(test, not(miri)),
    all_skl_tests,
    test_generic_sync_multiple_version_concurrent,
  ))]
  mod concurrent_tests {
    crate::__generic_multiple_version_map_tests!(go "sync_multiple_version_map": super::SkipMap<[u8], [u8]> => crate::tests::generic::TEST_OPTIONS);
  }

  #[cfg(any(
    all(test, not(miri)),
    all_skl_tests,
    test_generic_sync_multiple_version_concurrent_with_optimistic_freelist,
  ))]
  mod concurrent_tests_with_optimistic_freelist {
    crate::__generic_multiple_version_map_tests!(go "sync_multiple_version_map": super::SkipMap<[u8], [u8]> => crate::tests::generic::TEST_OPTIONS_WITH_OPTIMISTIC_FREELIST);
  }

  #[cfg(any(
    all(test, not(miri)),
    all_skl_tests,
    test_generic_sync_multiple_version_concurrent_with_pessimistic_freelist,
  ))]
  mod concurrent_tests_with_pessimistic_freelist {
    crate::__generic_multiple_version_map_tests!(go "sync_multiple_version_map": super::SkipMap<[u8], [u8]> => crate::tests::generic::TEST_OPTIONS_WITH_PESSIMISTIC_FREELIST);
  }

  type SkipList<K, V, C = Ascend> = super::super::list::SkipList<K, V, C, Allocator, RefCounter>;

  /// Iterator over the [`SkipMap`].
  pub type Iter<'a, K, V, S, C = Ascend> =
    super::super::iter::Iter<'a, K, V, S, C, Allocator, RefCounter>;

  /// Iterator over a subset of the [`SkipMap`].
  pub type Range<'a, K, V, S, Q, R, C = Ascend> =
    super::super::iter::Range<'a, K, V, S, C, Allocator, RefCounter, Q, R>;

  /// The entry reference of the [`SkipMap`].
  pub type Entry<'a, K, V, S, C = Ascend> =
    super::super::entry::EntryRef<'a, K, V, S, C, Allocator, RefCounter>;

  /// A fast, lock-free, thread-safe ARENA based `SkipMap` that supports multiple versions, forward and backward iteration.
  ///
  /// If you want to use in non-concurrent environment, you can use [`multiple_version::unsync::SkipMap`](crate::generic::multiple_version::unsync::SkipMap).
  #[repr(transparent)]
  pub struct SkipMap<K: ?Sized, V: ?Sized, C = Ascend>(SkipList<K, V, C>);

  impl<K: ?Sized, V: ?Sized, C: Clone> Clone for SkipMap<K, V, C> {
    #[inline]
    fn clone(&self) -> Self {
      Self(self.0.clone())
    }
  }

  impl<K: ?Sized, V: ?Sized, C> From<SkipList<K, V, C>> for SkipMap<K, V, C> {
    #[inline]
    fn from(list: SkipList<K, V, C>) -> Self {
      Self(list)
    }
  }

  impl<K: ?Sized + 'static, V: ?Sized + 'static, C> crate::traits::List for SkipMap<K, V, C> {
    type Constructable = SkipList<K, V, C>;

    #[inline]
    fn as_ref(&self) -> &Self::Constructable {
      &self.0
    }

    #[inline]
    fn as_mut(&mut self) -> &mut Self::Constructable {
      &mut self.0
    }

    #[inline]
    fn meta(
      &self,
    ) -> &<<Self::Constructable as crate::traits::Constructable>::Allocator as super::Sealed>::Meta
    {
      self.0.meta()
    }
  }

  impl<K, V, C> super::Map<K, V, C> for SkipMap<K, V, C>
  where
    K: ?Sized + 'static,
    V: ?Sized + 'static,
    C: 'static,
  {
    type Allocator = Allocator;
    type RefCounter = RefCounter;
  }
}

/// A fast, ARENA based `SkipMap` that supports multiple versions, forward and backward iteration.
///
/// - For concurrent environment, use [`sync::SkipMap`].
/// - For non-concurrent environment, use [`unsync::SkipMap`].
pub trait Map<K, V, C = Ascend>
where
  K: ?Sized + 'static,
  V: ?Sized + 'static,
  C: 'static,
  Self: Arena<Constructable = super::list::SkipList<K, V, C, Self::Allocator, Self::RefCounter>>,
  <Self::Allocator as Sealed>::Node: WithVersion,
{
  /// The allocator type used to allocate nodes in the map.
  type Allocator: Allocator;
  /// The reference counter type used in the map.
  type RefCounter: RefCounter;

  /// Try creates from a `SkipMap` from an allocator directly.
  ///
  /// This method is not the ideal constructor, it is recommended to use [`Builder`](super::Builder) to create a `SkipMap`,
  /// if you are not attempting to create multiple `SkipMap`s on the same allocator.
  ///
  /// Besides, the only way to reconstruct `SkipMap`s created by this method is to use the [`open_from_allocator(header: Header, arena: Self::Allocator, cmp: Self::Comparator)`](Map::open_from_allocator) method,
  /// users must save the header to reconstruct the `SkipMap` by their own.
  /// The header can be obtained by calling [`header`](Map::header) method.
  #[inline]
  fn create_from_allocator(arena: Self::Allocator, cmp: C) -> Result<Self, Error> {
    Self::try_create_from_allocator(arena, cmp)
  }

  /// Try open a `SkipMap` from an allocator directly.
  ///
  /// See documentation for [`create_from_allocator`](Map::create_from_allocator) for more information.
  ///
  /// ## Safety
  /// - The `header` must be the same as the one obtained from `SkipMap` when it was created.
  /// - The `K` and `V` types must be the same as the types used to create the map.
  #[inline]
  unsafe fn open_from_allocator(
    header: Header,
    arena: Self::Allocator,
    cmp: C,
  ) -> Result<Self, Error> {
    Self::try_open_from_allocator(arena, cmp, header)
  }

  /// Returns the header of the `SkipMap`, which can be used to reconstruct the `SkipMap`.
  ///
  /// By default, `SkipMap` will allocate meta, head node, and tail node in the ARENA,
  /// and the data section will be allocated after the tail node.
  ///
  /// This method will return the header in the ARENA.
  #[inline]
  fn header(&self) -> Option<&Header> {
    self.as_ref().header()
  }

  /// Returns the references for the `SkipMap`.
  #[inline]
  fn refs(&self) -> usize {
    self.as_ref().refs()
  }

  /// Returns the height of the highest tower within any of the nodes that
  /// have ever been allocated as part of this skiplist.
  #[inline]
  fn height(&self) -> u8 {
    self.as_ref().height()
  }

  /// Returns the number of entries in the map, this `len` includes all entry versions.
  ///
  /// If the map only contains tombstones, this method will not return `0` but the number of tombstones.
  #[inline]
  fn len(&self) -> usize {
    self.as_ref().len()
  }

  /// Returns `true` if the map is empty, if the map only contains tombstones, this method will also return `false`.
  #[inline]
  fn is_empty(&self) -> bool {
    self.len() == 0
  }

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

  /// Returns a random generated height.
  ///
  /// This method is useful when you want to check if the underlying allocator can allocate a node.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{generic::{multiple_version::{sync::SkipMap, Map}, Builder}, Arena};
  ///
  /// let map = Builder::new().with_capacity(1024).alloc::<SkipMap<[u8], [u8]>>().unwrap();
  /// let height = map.random_height();
  ///
  /// let needed = SkipMap::<[u8], [u8]>::estimated_node_size(height, b"k1".len(), b"k2".len());
  /// ```
  #[inline]
  fn random_height(&self) -> Height {
    self.as_ref().random_height()
  }

  /// Returns `true` if the map may contains an entry whose version is less than or equal to the given version.
  #[inline]
  fn may_contain_version(&self, v: Version) -> bool {
    self.as_ref().may_contain_version(v)
  }

  /// Returns `true` if the key exists in the map.
  ///
  /// This method will return `false` if the entry is marked as removed. If you want to check if the key exists even if it is marked as removed,
  /// you can use [`contains_key_with_tombstone`](Map::contains_key_with_tombstone).
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::generic::{multiple_version::{sync::SkipMap, Map}, Builder};
  ///
  /// let map = Builder::new().with_capacity(1024).alloc::<SkipMap<str, str>>().unwrap();
  ///
  /// map.insert(0, "hello", "world").unwrap();
  ///
  /// map.get_or_remove(1, "hello").unwrap();
  ///
  /// assert!(!map.contains_key(1, "hello"));
  /// assert!(map.contains_key_with_tombstone(1, "hello"));
  /// ```
  #[inline]
  fn contains_key<'a, Q>(&'a self, version: Version, key: &Q) -> bool
  where
    K: Type,
    V: Type,
    Q: ?Sized,
    C: TypeRefQueryComparator<'a, K, Q>,
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
  /// use skl::generic::{multiple_version::{sync::SkipMap, Map}, Builder};
  ///
  /// let map = Builder::new().with_capacity(1024).alloc::<SkipMap<str, str>>().unwrap();
  ///
  /// map.insert(0, "hello", "world").unwrap();
  ///
  /// map.get_or_remove(1, "hello").unwrap();
  ///
  /// assert!(!map.contains_key(1, "hello"));
  /// assert!(map.contains_key_with_tombstone(1, "hello"));
  /// ```
  #[inline]
  fn contains_key_with_tombstone<'a, Q>(&'a self, version: Version, key: &Q) -> bool
  where
    K: Type,
    V: Type,
    Q: ?Sized,
    C: TypeRefQueryComparator<'a, K, Q>,
  {
    if !self.may_contain_version(version) {
      return false;
    }

    self.as_ref().contains_key_with_tombstone(version, key)
  }

  /// Returns the first entry in the map.
  #[inline]
  fn first<'a>(
    &'a self,
    version: Version,
  ) -> Option<EntryRef<'a, K, V, Active, C, Self::Allocator, Self::RefCounter>>
  where
    K: Type,
    V: Type,
    C: TypeRefComparator<'a, K>,
  {
    if !self.may_contain_version(version) {
      return None;
    }

    self.as_ref().first(version)
  }

  /// Returns the last entry in the map.
  #[inline]
  fn last<'a>(
    &'a self,
    version: Version,
  ) -> Option<EntryRef<'a, K, V, Active, C, Self::Allocator, Self::RefCounter>>
  where
    K: Type,
    V: Type,
    C: TypeRefComparator<'a, K>,
  {
    if !self.may_contain_version(version) {
      return None;
    }

    self.as_ref().last(version)
  }

  /// Returns the first entry in the map. The returned entry may not be in valid state. (i.e. the entry is removed)
  ///
  /// The difference between [`first`](Map::first) and `first_with_tombstone` is that `first_with_tombstone` will return the value even if
  /// the entry is removed or not in a valid state.
  #[inline]
  fn first_with_tombstone<'a>(
    &'a self,
    version: Version,
  ) -> Option<EntryRef<'a, K, V, MaybeTombstone, C, Self::Allocator, Self::RefCounter>>
  where
    K: Type,
    V: Type,
    C: TypeRefComparator<'a, K>,
  {
    if !self.may_contain_version(version) {
      return None;
    }

    self.as_ref().first_with_tombstone(version)
  }

  /// Returns the last entry in the map. The returned entry may not be in valid state. (i.e. the entry is removed)
  ///
  /// The difference between [`last`](Map::last) and `last_with_tombstone` is that `last_with_tombstone` will return the value even if
  /// the entry is removed or not in a valid state.
  #[inline]
  fn last_with_tombstone<'a>(
    &'a self,
    version: Version,
  ) -> Option<EntryRef<'a, K, V, MaybeTombstone, C, Self::Allocator, Self::RefCounter>>
  where
    K: Type,
    V: Type,
    C: TypeRefComparator<'a, K>,
  {
    if !self.may_contain_version(version) {
      return None;
    }

    self.as_ref().last_with_tombstone(version)
  }

  /// Returns the value associated with the given key, if it exists.
  ///
  /// This method will return `None` if the entry is marked as removed. If you want to get the entry even if it is marked as removed,
  /// you can use [`get_with_tombstone`](Map::get_with_tombstone).
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::generic::{multiple_version::{sync::SkipMap, Map}, Builder};
  ///
  /// let map = Builder::new().with_capacity(1024).alloc::<SkipMap<str, str>>().unwrap();
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
  fn get<'a, Q>(
    &'a self,
    version: Version,
    key: &Q,
  ) -> Option<EntryRef<'a, K, V, Active, C, Self::Allocator, Self::RefCounter>>
  where
    K: Type,
    V: Type,
    Q: ?Sized,
    C: TypeRefQueryComparator<'a, K, Q>,
  {
    if !self.may_contain_version(version) {
      return None;
    }

    self.as_ref().get(version, key)
  }

  /// Returns the value associated with the given key, if it exists.
  ///
  /// The difference between `get` and `get_with_tombstone` is that `get_with_tombstone` will return the value even if the entry is removed.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::generic::{multiple_version::{sync::SkipMap, Map}, Builder};
  ///
  /// let map = Builder::new().with_capacity(1024).alloc::<SkipMap<str, str>>().unwrap();
  ///
  /// map.insert(0, "hello", "world").unwrap();
  ///
  /// map.get_or_remove(1, "hello").unwrap();
  ///
  /// assert!(map.get(1, "hello").is_none());
  ///
  /// let ent = map.get_with_tombstone(1, "hello").unwrap();
  /// // value is None because the entry is marked as removed.
  /// assert!(ent.value().is_none());
  /// ```
  #[inline]
  fn get_with_tombstone<'a, Q>(
    &'a self,
    version: Version,
    key: &Q,
  ) -> Option<EntryRef<'a, K, V, MaybeTombstone, C, Self::Allocator, Self::RefCounter>>
  where
    K: Type,
    V: Type,
    Q: ?Sized,
    C: TypeRefQueryComparator<'a, K, Q>,
  {
    if !self.may_contain_version(version) {
      return None;
    }

    self.as_ref().get_with_tombstone(version, key)
  }

  /// Returns an `EntryRef` pointing to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  #[inline]
  fn upper_bound<'a, Q>(
    &'a self,
    version: Version,
    upper: Bound<&Q>,
  ) -> Option<EntryRef<'a, K, V, Active, C, Self::Allocator, Self::RefCounter>>
  where
    K: Type,
    V: Type,
    Q: ?Sized,
    C: TypeRefQueryComparator<'a, K, Q>,
  {
    if !self.may_contain_version(version) {
      return None;
    }

    self.as_ref().upper_bound(version, upper)
  }

  /// Returns an `EntryRef` pointing to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  #[inline]
  fn lower_bound<'a, Q>(
    &'a self,
    version: Version,
    lower: Bound<&Q>,
  ) -> Option<EntryRef<'a, K, V, Active, C, Self::Allocator, Self::RefCounter>>
  where
    K: Type,
    V: Type,
    Q: ?Sized,
    C: TypeRefQueryComparator<'a, K, Q>,
  {
    if !self.may_contain_version(version) {
      return None;
    }

    self.as_ref().lower_bound(version, lower)
  }

  /// Returns an `EntryRef` pointing to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  ///
  /// The difference between [`upper_bound`](Map::upper_bound) and `upper_bound_with_tombstone` is that `upper_bound_with_tombstone` will return the value even if the entry is removed.
  #[inline]
  fn upper_bound_with_tombstone<'a, Q>(
    &'a self,
    version: Version,
    upper: Bound<&Q>,
  ) -> Option<EntryRef<'a, K, V, MaybeTombstone, C, Self::Allocator, Self::RefCounter>>
  where
    K: Type,
    V: Type,
    Q: ?Sized,
    C: TypeRefQueryComparator<'a, K, Q>,
  {
    if !self.may_contain_version(version) {
      return None;
    }

    self.as_ref().upper_bound_with_tombstone(version, upper)
  }

  /// Returns an `EntryRef` pointing to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  ///
  /// The difference between [`lower_bound`](Map::lower_bound) and `lower_bound_with_tombstone` is that `lower_bound_with_tombstone` will return the value even if the entry is removed.
  #[inline]
  fn lower_bound_with_tombstone<'a, Q>(
    &'a self,
    version: Version,
    lower: Bound<&Q>,
  ) -> Option<EntryRef<'a, K, V, MaybeTombstone, C, Self::Allocator, Self::RefCounter>>
  where
    K: Type,
    V: Type,
    Q: ?Sized,
    C: TypeRefQueryComparator<'a, K, Q>,
  {
    if !self.may_contain_version(version) {
      return None;
    }

    self.as_ref().lower_bound_with_tombstone(version, lower)
  }

  /// Returns a new iterator, this iterator will yield the latest version of all entries in the map less or equal to the given version.
  #[inline]
  fn iter(&self, version: Version) -> Iter<'_, K, V, Active, C, Self::Allocator, Self::RefCounter>
  where
    K: Type,
    V: Type,
  {
    self.as_ref().iter(version)
  }

  /// Returns a new iterator, this iterator will yield all versions for all entries in the map less or equal to the given version.
  #[inline]
  fn iter_all(
    &self,
    version: Version,
  ) -> Iter<'_, K, V, MaybeTombstone, C, Self::Allocator, Self::RefCounter>
  where
    K: Type,
    V: Type,
  {
    self.as_ref().iter_all(version)
  }

  /// Returns a iterator that within the range, this iterator will yield the latest version of all entries in the range less or equal to the given version.
  #[inline]
  fn range<Q, R>(
    &self,
    version: Version,
    range: R,
  ) -> Range<'_, K, V, Active, C, Self::Allocator, Self::RefCounter, Q, R>
  where
    K: Type,
    V: Type,
    Q: ?Sized,
    R: RangeBounds<Q>,
  {
    self.as_ref().range(version, range)
  }

  /// Returns a iterator that within the range, this iterator will yield all versions for all entries in the range less or equal to the given version.
  #[inline]
  fn range_all<Q, R>(
    &self,
    version: Version,
    range: R,
  ) -> Range<'_, K, V, MaybeTombstone, C, Self::Allocator, Self::RefCounter, Q, R>
  where
    K: Type,
    V: Type,
    Q: ?Sized,
    R: RangeBounds<Q>,
  {
    self.as_ref().range_all(version, range)
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
  ) -> Result<
    Option<EntryRef<'a, K, V, Active, C, Self::Allocator, Self::RefCounter>>,
    Among<K::Error, V::Error, Error>,
  >
  where
    K: Type + 'b,
    V: Type + 'b,
    C: TypeRefComparator<'a, K>,
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
  /// use skl::{generic::{multiple_version::{sync::SkipMap, Map}, Builder}, Arena};
  ///
  /// let map = Builder::new().with_capacity(1024).alloc::<SkipMap<str, str>>().unwrap();
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
  ) -> Result<
    Option<EntryRef<'a, K, V, Active, C, Self::Allocator, Self::RefCounter>>,
    Among<K::Error, V::Error, Error>,
  >
  where
    K: Type + 'b,
    V: Type + 'b,
    C: TypeRefComparator<'a, K>,
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
  /// use skl::{generic::{multiple_version::{sync::SkipMap, Map}, Builder}, ValueBuilder};
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
  /// let l = Builder::new().with_capacity(1024).alloc::<SkipMap<[u8], [u8]>>().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size, |val: &mut skl::VacantBuffer<'_>| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(encoded_size)
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
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, E>>,
  ) -> Result<
    Option<EntryRef<'a, K, V, Active, C, Self::Allocator, Self::RefCounter>>,
    Among<K::Error, E, Error>,
  >
  where
    K: Type + 'b,
    V: Type + 'b,
    C: TypeRefComparator<'a, K>,
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
  /// use skl::{generic::{multiple_version::{sync::SkipMap, Map}, Builder}, ValueBuilder, Arena};
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
  /// let l = Builder::new().with_capacity(1024).alloc::<SkipMap<[u8], [u8]>>().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size, |val: &mut skl::VacantBuffer<'_>| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(encoded_size)
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
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, E>>,
  ) -> Result<
    Option<EntryRef<'a, K, V, Active, C, Self::Allocator, Self::RefCounter>>,
    Among<K::Error, E, Error>,
  >
  where
    K: Type + 'b,
    V: Type + 'b,
    C: TypeRefComparator<'a, K>,
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
  ) -> Result<
    Option<EntryRef<'a, K, V, Active, C, Self::Allocator, Self::RefCounter>>,
    Among<K::Error, V::Error, Error>,
  >
  where
    K: Type + 'b,
    V: Type + 'b,
    C: TypeRefComparator<'a, K>,
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
  ) -> Result<
    Option<EntryRef<'a, K, V, Active, C, Self::Allocator, Self::RefCounter>>,
    Among<K::Error, V::Error, Error>,
  >
  where
    K: Type + 'b,
    V: Type + 'b,
    C: TypeRefComparator<'a, K>,
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
  /// use skl::{generic::{multiple_version::{sync::SkipMap, Map}, Builder}, ValueBuilder};
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
  /// let l = Builder::new().with_capacity(1024).alloc::<SkipMap<[u8], [u8]>>().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size, |val: &mut skl::VacantBuffer<'_>| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(encoded_size)
  /// });
  /// l.get_or_insert_with_value_builder::<core::convert::Infallible>(1, b"alice".as_slice(), vb)
  /// .unwrap();
  /// ```
  #[inline]
  fn get_or_insert_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    version: Version,
    key: impl Into<MaybeStructured<'b, K>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, E>>,
  ) -> Result<
    Option<EntryRef<'a, K, V, Active, C, Self::Allocator, Self::RefCounter>>,
    Among<K::Error, E, Error>,
  >
  where
    K: Type + 'b,
    V: Type + 'b,
    C: TypeRefComparator<'a, K>,
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
  /// use skl::{generic::{multiple_version::{sync::SkipMap, Map}, Builder}, ValueBuilder, Arena};
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
  /// let l = Builder::new().with_capacity(1024).alloc::<SkipMap<[u8], [u8]>>().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size, |val: &mut skl::VacantBuffer<'_>| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(encoded_size)
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
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, E>>,
  ) -> Result<
    Option<EntryRef<'a, K, V, Active, C, Self::Allocator, Self::RefCounter>>,
    Among<K::Error, E, Error>,
  >
  where
    K: Type + 'b,
    V: Type + 'b,
    C: TypeRefComparator<'a, K>,
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
  /// use skl::{generic::{multiple_version::{sync::SkipMap, Map}, Builder}, KeyBuilder, ValueBuilder};
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
  /// let l = Builder::new().with_capacity(1024).alloc::<SkipMap<[u8], [u8]>>().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |key: &mut skl::VacantBuffer<'_>| {
  ///   key.put_slice(b"alice").unwrap();
  ///   Ok(5)
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size, |val: &mut skl::VacantBuffer<'_>| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(encoded_size)
  /// });
  ///
  /// l.insert_with_builders::<(), ()>(1, kb, vb)
  /// .unwrap();
  /// ```
  #[inline]
  fn insert_with_builders<'a, KE, VE>(
    &'a self,
    version: Version,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, VE>>,
  ) -> Result<
    Option<EntryRef<'a, K, V, Active, C, Self::Allocator, Self::RefCounter>>,
    Among<KE, VE, Error>,
  >
  where
    K: Type,
    V: Type,
    C: TypeRefComparator<'a, K>,
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
  /// use skl::{generic::{multiple_version::{sync::SkipMap, Map}, Builder}, KeyBuilder, ValueBuilder, Arena};
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
  /// let l = Builder::new().with_capacity(1024).alloc::<SkipMap<[u8], [u8]>>().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |key: &mut skl::VacantBuffer<'_>| {
  ///   key.put_slice(b"alice").unwrap();
  ///   Ok(5)
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size, |val: &mut skl::VacantBuffer<'_>| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(encoded_size)
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
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, VE>>,
  ) -> Result<
    Option<EntryRef<'a, K, V, Active, C, Self::Allocator, Self::RefCounter>>,
    Among<KE, VE, Error>,
  >
  where
    K: Type,
    V: Type,
    C: TypeRefComparator<'a, K>,
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
  /// use skl::{generic::{multiple_version::{sync::SkipMap, Map}, Builder}, KeyBuilder, ValueBuilder};
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
  /// let l = Builder::new().with_capacity(1024).alloc::<SkipMap<[u8], [u8]>>().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |key: &mut skl::VacantBuffer<'_>| {
  ///   key.put_slice(b"alice").unwrap();
  ///   Ok(5)
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size, |val: &mut skl::VacantBuffer<'_>| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(encoded_size)
  /// });
  ///
  /// l.get_or_insert_with_builders::<(), ()>(1, kb, vb)
  /// .unwrap();
  /// ```
  #[inline]
  fn get_or_insert_with_builders<'a, KE, VE>(
    &'a self,
    version: Version,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, VE>>,
  ) -> Result<
    Option<EntryRef<'a, K, V, Active, C, Self::Allocator, Self::RefCounter>>,
    Among<KE, VE, Error>,
  >
  where
    K: Type,
    V: Type,
    C: TypeRefComparator<'a, K>,
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
  /// use skl::{generic::{multiple_version::{sync::SkipMap, Map}, Builder}, KeyBuilder, ValueBuilder, Arena};
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
  /// let l = Builder::new().with_capacity(1024).alloc::<SkipMap<[u8], [u8]>>().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |key: &mut skl::VacantBuffer<'_>| {
  ///   key.put_slice(b"alice").unwrap();
  ///   Ok(5)
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size, |val: &mut skl::VacantBuffer<'_>| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(encoded_size)
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
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, VE>>,
  ) -> Result<
    Option<EntryRef<'a, K, V, Active, C, Self::Allocator, Self::RefCounter>>,
    Among<KE, VE, Error>,
  >
  where
    K: Type,
    V: Type,
    C: TypeRefComparator<'a, K>,
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
  ) -> Result<
    Option<EntryRef<'a, K, V, Active, C, Self::Allocator, Self::RefCounter>>,
    Either<K::Error, Error>,
  >
  where
    K: Type + 'b,
    V: Type,
    C: TypeRefComparator<'a, K>,
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
  ) -> Result<
    Option<EntryRef<'a, K, V, Active, C, Self::Allocator, Self::RefCounter>>,
    Either<K::Error, Error>,
  >
  where
    K: Type + 'b,
    V: Type,
    C: TypeRefComparator<'a, K>,
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
  ) -> Result<
    Option<EntryRef<'a, K, V, Active, C, Self::Allocator, Self::RefCounter>>,
    Either<K::Error, Error>,
  >
  where
    K: Type + 'b,
    V: Type,
    C: TypeRefComparator<'a, K>,
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
  /// use skl::{generic::{multiple_version::{sync::SkipMap, Map}, Builder}, Arena};
  ///
  /// let map = Builder::new().with_capacity(1024).alloc::<SkipMap<str, str>>().unwrap();
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
  ) -> Result<
    Option<EntryRef<'a, K, V, Active, C, Self::Allocator, Self::RefCounter>>,
    Either<K::Error, Error>,
  >
  where
    K: Type + 'b,
    V: Type,
    C: TypeRefComparator<'a, K>,
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
  /// use skl::{generic::{multiple_version::{sync::SkipMap, Map}, Builder}, KeyBuilder};
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
  /// let l = Builder::new().with_capacity(1024).alloc::<SkipMap<[u8], [u8]>>().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |key: &mut skl::VacantBuffer<'_>| {
  ///   key.put_slice(b"alice").unwrap();
  ///   Ok(5)
  /// });
  /// l.get_or_remove_with_builder::<core::convert::Infallible>(1, kb)
  /// .unwrap();
  /// ```
  #[inline]
  fn get_or_remove_with_builder<'a, 'b: 'a, E>(
    &'a self,
    version: Version,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, E>>,
  ) -> Result<
    Option<EntryRef<'a, K, V, Active, C, Self::Allocator, Self::RefCounter>>,
    Either<E, Error>,
  >
  where
    K: Type,
    V: Type,
    C: TypeRefComparator<'a, K>,
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
  /// use skl::{generic::{multiple_version::{sync::SkipMap, Map}, Builder}, KeyBuilder, Arena};
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
  /// let l = Builder::new().with_capacity(1024).alloc::<SkipMap<[u8], [u8]>>().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |key: &mut skl::VacantBuffer<'_>| {
  ///   key.put_slice(b"alice").unwrap();
  ///   Ok(5)
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
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, E>>,
  ) -> Result<
    Option<EntryRef<'a, K, V, Active, C, Self::Allocator, Self::RefCounter>>,
    Either<E, Error>,
  >
  where
    K: Type,
    V: Type,
    C: TypeRefComparator<'a, K>,
  {
    self
      .as_ref()
      .get_or_remove_at_height_with_builder(version, height, key_builder)
  }
}
