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
  allocator::{Allocator, Sealed, WithoutVersion},
  error::Error,
  generic::Active,
  ref_counter::RefCounter,
  Arena, Header, Height, KeyBuilder, MaybeTombstone, ValueBuilder, MIN_VERSION,
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
  pub use crate::unsync::{map::Allocator, RefCounter};

  #[cfg(any(all(test, not(miri)), all_skl_tests, test_generic_unsync_map,))]
  mod tests {
    crate::__generic_map_tests!("unsync_map": super::SkipMap<[u8], [u8]>);
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

  /// A fast, ARENA based `SkipMap` that supports forward and backward iteration.
  ///
  /// If you want to use in concurrent environment, you can use [`unique::sync::SkipMap`](crate::generic::unique::sync::SkipMap).
  #[repr(transparent)]
  pub struct SkipMap<K: ?Sized, V: ?Sized, C = Ascend>(SkipList<K, V, C>);

  impl<K: ?Sized, V: ?Sized> Clone for SkipMap<K, V> {
    #[inline]
    fn clone(&self) -> Self {
      Self(self.0.clone())
    }
  }

  impl<K: ?Sized, V: ?Sized> From<SkipList<K, V>> for SkipMap<K, V> {
    #[inline]
    fn from(list: SkipList<K, V>) -> Self {
      Self(list)
    }
  }

  impl<K: ?Sized + 'static, V: ?Sized + 'static> crate::traits::List for SkipMap<K, V> {
    type Constructable = SkipList<K, V>;

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

  impl<K, V> super::Map<K, V> for SkipMap<K, V>
  where
    K: ?Sized + 'static,
    V: ?Sized + 'static,
  {
    type Allocator = Allocator;
    type RefCounter = RefCounter;
  }
}

/// Implementations for concurrent environments.
pub mod sync {
  use crate::generic::Ascend;
  pub use crate::sync::{map::Allocator, RefCounter};

  #[cfg(any(all(test, not(miri)), all_skl_tests, test_generic_sync_map,))]
  mod tests {
    crate::__generic_map_tests!("sync_map": super::SkipMap<[u8], [u8]>);
  }

  #[cfg(any(all(test, not(miri)), all_skl_tests, test_generic_sync_map_concurrent,))]
  mod concurrent_tests {
    crate::__generic_map_tests!(go "sync_map": super::SkipMap<[u8], [u8]> => crate::tests::generic::TEST_OPTIONS);
  }

  #[cfg(any(
    all(test, not(miri)),
    all_skl_tests,
    test_generic_sync_map_concurrent_with_optimistic_freelist,
  ))]
  mod concurrent_tests_with_optimistic_freelist {
    crate::__generic_map_tests!(go "sync_map": super::SkipMap<[u8], [u8]> => crate::tests::generic::TEST_OPTIONS_WITH_OPTIMISTIC_FREELIST);
  }

  #[cfg(any(
    all(test, not(miri)),
    all_skl_tests,
    test_generic_sync_map_concurrent_with_pessimistic_freelist,
  ))]
  mod concurrent_tests_with_pessimistic_freelist {
    crate::__generic_map_tests!(go "sync_map": super::SkipMap<[u8], [u8]> => crate::tests::generic::TEST_OPTIONS_WITH_PESSIMISTIC_FREELIST);
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

  /// A fast, lock-free, thread-safe ARENA based `SkipMap` that supports forward and backward iteration.
  ///
  /// If you want to use in non-concurrent environment, you can use [`unique::unsync::SkipMap`](crate::generic::unique::unsync::SkipMap).
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

/// A fast, ARENA based `SkipMap` that supports forward and backward iteration.
///
/// - For concurrent environment, use [`sync::SkipMap`].
/// - For non-concurrent environment, use [`unsync::SkipMap`].
pub trait Map<K, V, C = Ascend>
where
  K: ?Sized + 'static,
  V: ?Sized + 'static,
  C: 'static,
  Self: Arena<Constructable = super::list::SkipList<K, V, C, Self::Allocator, Self::RefCounter>>,
  <Self::Allocator as Sealed>::Node: WithoutVersion,
{
  /// The allocator used to allocate nodes in the `SkipMap`.
  type Allocator: Allocator;
  /// The reference counter of the `SkipMap`.
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

  /// Returns the height of the highest tower within any of the nodes that
  /// have ever been allocated as part of this skiplist.
  #[inline]
  fn height(&self) -> u8 {
    self.as_ref().height()
  }

  /// Returns the number of entries in the map, this `len` includes all tombstones.
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

  /// Returns a random generated height.
  ///
  /// This method is useful when you want to check if the underlying allocator can allocate a node.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{generic::{unique::{sync::SkipMap, Map}, Builder}, Arena};
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

  /// Returns the references for the `SkipMap`.
  #[inline]
  fn refs(&self) -> usize {
    self.as_ref().refs()
  }

  /// Returns `true` if the key exists in the map.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::generic::{unique::{unsync::SkipMap, Map}, Builder};
  ///
  /// let map = Builder::new().with_capacity(1024).alloc::<SkipMap::<str, str>>().unwrap();
  ///
  /// map.insert("hello", "world").unwrap();
  ///
  /// map.remove("hello").unwrap();
  ///
  /// assert!(!map.contains_key("hello"));
  /// ```
  #[inline]
  fn contains_key<'a, Q>(&'a self, key: &Q) -> bool
  where
    K: Type,
    V: Type,
    Q: ?Sized,
    C: TypeRefQueryComparator<'a, K, Q>,
  {
    self.as_ref().contains_key(MIN_VERSION, key)
  }

  /// Returns `true` if the key exists in the map, even if it is marked as removed.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::generic::{unique::{sync::SkipMap, Map}, Builder};
  ///
  /// let map = Builder::new().with_capacity(1024).alloc::<SkipMap<str, str>>().unwrap();
  ///
  /// map.insert("hello", "world").unwrap();
  ///
  /// map.remove("hello").unwrap();
  ///
  /// assert!(!map.contains_key("hello"));
  /// assert!(map.contains_key_with_tombstone("hello"));
  /// ```
  #[inline]
  fn contains_key_with_tombstone<'a, Q>(&'a self, key: &Q) -> bool
  where
    K: Type,
    V: Type,
    Q: ?Sized,
    C: TypeRefQueryComparator<'a, K, Q>,
  {
    self.as_ref().contains_key_with_tombstone(MIN_VERSION, key)
  }

  /// Returns the first entry in the map.
  #[inline]
  fn first<'a>(&'a self) -> Option<EntryRef<'a, K, V, Active, C, Self::Allocator, Self::RefCounter>>
  where
    K: Type,
    V: Type,
    C: TypeRefComparator<'a, K>,
  {
    self.as_ref().first(MIN_VERSION)
  }

  /// Returns the last entry in the map.
  #[inline]
  fn last<'a>(&'a self) -> Option<EntryRef<'a, K, V, Active, C, Self::Allocator, Self::RefCounter>>
  where
    K: Type,
    V: Type,
    C: TypeRefComparator<'a, K>,
  {
    self.as_ref().last(MIN_VERSION)
  }

  /// Returns the first entry in the map. The returned entry may not be in valid state. (i.e. the entry is removed)
  ///
  /// The difference between [`first`](Map::first) and `first_with_tombstone` is that `first_with_tombstone` will return the value even if
  /// the entry is removed or not in a valid state.
  #[inline]
  fn first_with_tombstone<'a>(
    &'a self,
  ) -> Option<EntryRef<'a, K, V, MaybeTombstone, C, Self::Allocator, Self::RefCounter>>
  where
    K: Type,
    V: Type,
    C: TypeRefComparator<'a, K>,
  {
    self.as_ref().first_with_tombstone(0)
  }

  /// Returns the last entry in the map. The returned entry may not be in valid state. (i.e. the entry is removed)
  ///
  /// The difference between [`last`](Map::last) and `last_with_tombstone` is that `last_with_tombstone` will return the value even if
  /// the entry is removed or not in a valid state.
  #[inline]
  fn last_with_tombstone<'a>(
    &'a self,
  ) -> Option<EntryRef<'a, K, V, MaybeTombstone, C, Self::Allocator, Self::RefCounter>>
  where
    K: Type,
    V: Type,
    C: TypeRefComparator<'a, K>,
  {
    self.as_ref().last_with_tombstone(0)
  }

  /// Returns the value associated with the given key, if it exists.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::generic::{unique::{sync::SkipMap, Map}, Builder};
  ///
  /// let map = Builder::new().with_capacity(1024).alloc::<SkipMap<str, str>>().unwrap();
  ///
  /// map.insert("hello", "world").unwrap();
  ///
  /// let ent = map.get("hello").unwrap();
  /// assert_eq!(ent.value(), "world");
  ///
  /// map.remove("hello").unwrap();
  ///
  /// assert!(map.get("hello").is_none());
  /// ```
  #[inline]
  fn get<'a, Q>(
    &'a self,
    key: &Q,
  ) -> Option<EntryRef<'a, K, V, Active, C, Self::Allocator, Self::RefCounter>>
  where
    K: Type,
    V: Type,
    Q: ?Sized,
    C: TypeRefQueryComparator<'a, K, Q>,
  {
    self.as_ref().get(MIN_VERSION, key)
  }

  /// Returns the value associated with the given key, if it exists.
  ///
  /// The difference between `get` and `get_with_tombstone` is that `get_with_tombstone` will return the value even if the entry is removed.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::generic::{unique::{sync::SkipMap, Map}, Builder};
  ///
  /// let map = Builder::new().with_capacity(1024).alloc::<SkipMap<str, str>>().unwrap();
  ///
  /// map.insert("hello", "world").unwrap();
  ///
  /// map.remove("hello").unwrap();
  ///
  /// assert!(map.get("hello").is_none());
  ///
  /// let ent = map.get_with_tombstone("hello").unwrap();
  /// // value is None because the entry is marked as removed.
  /// assert!(ent.value().is_none());
  /// ```
  #[inline]
  fn get_with_tombstone<'a, Q>(
    &'a self,
    key: &Q,
  ) -> Option<EntryRef<'a, K, V, MaybeTombstone, C, Self::Allocator, Self::RefCounter>>
  where
    K: Type,
    V: Type,
    Q: ?Sized,
    C: TypeRefQueryComparator<'a, K, Q>,
  {
    self.as_ref().get_with_tombstone(MIN_VERSION, key)
  }

  /// Returns an `EntryRef` pointing to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  #[inline]
  fn upper_bound<'a, Q>(
    &'a self,
    upper: Bound<&Q>,
  ) -> Option<EntryRef<'a, K, V, Active, C, Self::Allocator, Self::RefCounter>>
  where
    K: Type,
    V: Type,
    Q: ?Sized,
    C: TypeRefQueryComparator<'a, K, Q>,
  {
    self.as_ref().upper_bound(MIN_VERSION, upper)
  }

  /// Returns an `EntryRef` pointing to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  #[inline]
  fn lower_bound<'a, Q>(
    &'a self,
    lower: Bound<&Q>,
  ) -> Option<EntryRef<'a, K, V, Active, C, Self::Allocator, Self::RefCounter>>
  where
    K: Type,
    V: Type,
    Q: ?Sized,
    C: TypeRefQueryComparator<'a, K, Q>,
  {
    self.as_ref().lower_bound(MIN_VERSION, lower)
  }

  /// Returns an `EntryRef` pointing to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  ///
  /// The difference between [`upper_bound`](Map::upper_bound) and `upper_bound_with_tombstone` is that `upper_bound_with_tombstone` will return the value even if the entry is removed.
  #[inline]
  fn upper_bound_with_tombstone<'a, Q>(
    &'a self,
    upper: Bound<&Q>,
  ) -> Option<EntryRef<'a, K, V, MaybeTombstone, C, Self::Allocator, Self::RefCounter>>
  where
    K: Type,
    V: Type,
    Q: ?Sized,
    C: TypeRefQueryComparator<'a, K, Q>,
  {
    self.as_ref().upper_bound_with_tombstone(MIN_VERSION, upper)
  }

  /// Returns an `EntryRef` pointing to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  ///
  /// The difference between [`lower_bound`](Map::lower_bound) and `lower_bound_with_tombstone` is that `lower_bound_with_tombstone` will return the value even if the entry is removed.
  #[inline]
  fn lower_bound_with_tombstone<'a, Q>(
    &'a self,
    lower: Bound<&Q>,
  ) -> Option<EntryRef<'a, K, V, MaybeTombstone, C, Self::Allocator, Self::RefCounter>>
  where
    K: Type,
    V: Type,
    Q: ?Sized,
    C: TypeRefQueryComparator<'a, K, Q>,
  {
    self.as_ref().lower_bound_with_tombstone(MIN_VERSION, lower)
  }

  /// Returns a new iterator, this iterator will yield only active entries of all entries in the map less or equal to the given version.
  #[inline]
  fn iter(&self) -> Iter<'_, K, V, Active, C, Self::Allocator, Self::RefCounter>
  where
    K: Type,
    V: Type,
  {
    self.as_ref().iter(MIN_VERSION)
  }

  /// Returns a new iterator, this iterator will yield with tombstones for all entries in the map less or equal to the given version.
  #[inline]
  fn iter_with_tombstone(
    &self,
  ) -> Iter<'_, K, V, MaybeTombstone, C, Self::Allocator, Self::RefCounter>
  where
    K: Type,
    V: Type,
  {
    self.as_ref().iter_all(0)
  }

  /// Returns a iterator that within the range, this iterator will yield only active entries of all entries in the range less or equal to the given version.
  #[inline]
  fn range<Q, R>(
    &self,
    range: R,
  ) -> Range<'_, K, V, Active, C, Self::Allocator, Self::RefCounter, Q, R>
  where
    K: Type,
    V: Type,
    Q: ?Sized,
    R: RangeBounds<Q>,
  {
    self.as_ref().range(MIN_VERSION, range)
  }

  /// Returns a iterator that within the range, this iterator will yield with tombstones for all entries in the range less or equal to the given version.
  #[inline]
  fn range_with_tombstone<Q, R>(
    &self,
    range: R,
  ) -> Range<'_, K, V, MaybeTombstone, C, Self::Allocator, Self::RefCounter, Q, R>
  where
    K: Type,
    V: Type,
    Q: ?Sized,
    R: RangeBounds<Q>,
  {
    self.as_ref().range_all(MIN_VERSION, range)
  }

  /// Upserts a new key-value pair if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert`](Map::get_or_insert), this method will update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  #[inline]
  fn insert<'a, 'b: 'a>(
    &'a self,
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
    self.insert_at_height(self.random_height(), key, value)
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
  /// use skl::{generic::{unique::{sync::SkipMap, Map}, Builder}, Arena};
  ///
  /// let map = Builder::new().with_capacity(1024).alloc::<SkipMap<str, str>>().unwrap();
  ///
  /// let height = map.random_height();
  /// map.insert_at_height(height, "hello", "world").unwrap();
  /// ```
  #[inline]
  fn insert_at_height<'a, 'b: 'a>(
    &'a self,
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
      .insert_at_height(MIN_VERSION, height, key, value)
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
  /// use skl::{generic::{unique::{sync::SkipMap, Map}, Builder}, ValueBuilder};
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
  /// l.insert_with_value_builder::<core::convert::Infallible>(b"alice".as_slice(), vb)
  /// .unwrap();
  /// ```
  #[inline]
  #[allow(single_use_lifetimes)]
  fn insert_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
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
    self.insert_at_height_with_value_builder(self.random_height(), key, value_builder)
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
  /// use skl::{generic::{unique::{sync::SkipMap, Map}, Builder}, ValueBuilder, Arena};
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
  /// l.insert_at_height_with_value_builder::<core::convert::Infallible>(height, b"alice".as_slice(), vb)
  /// .unwrap();
  /// ```
  #[inline]
  #[allow(single_use_lifetimes)]
  fn insert_at_height_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
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
      .insert_at_height_with_value_builder(MIN_VERSION, height, key, value_builder)
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
    self.get_or_insert_at_height(self.random_height(), key, value)
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
      .get_or_insert_at_height(MIN_VERSION, height, key, value)
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
  /// use skl::{generic::{unique::{sync::SkipMap, Map}, Builder}, ValueBuilder};
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
  /// l.get_or_insert_with_value_builder::<core::convert::Infallible>(b"alice".as_slice(), vb)
  /// .unwrap();
  /// ```
  #[inline]
  #[allow(single_use_lifetimes)]
  fn get_or_insert_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
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
    self.get_or_insert_at_height_with_value_builder(self.random_height(), key, value_builder)
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
  /// use skl::{generic::{unique::{sync::SkipMap, Map}, Builder}, ValueBuilder, Arena};
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
  /// l.get_or_insert_at_height_with_value_builder::<core::convert::Infallible>(height, b"alice".as_slice(), vb)
  /// .unwrap();
  /// ```
  #[inline]
  #[allow(single_use_lifetimes)]
  fn get_or_insert_at_height_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
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
    self.as_ref().get_or_insert_at_height_with_value_builder(
      MIN_VERSION,
      height,
      key,
      value_builder,
    )
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
  /// use skl::{generic::{unique::{sync::SkipMap, Map}, Builder}, KeyBuilder, ValueBuilder};
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
  /// l.insert_with_builders::<(), ()>(kb, vb)
  /// .unwrap();
  /// ```
  #[inline]
  fn insert_with_builders<'a, KE, VE>(
    &'a self,
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
    self.insert_at_height_with_builders(self.random_height(), key_builder, value_builder)
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
  /// use skl::{generic::{unique::{sync::SkipMap, Map}, Builder}, KeyBuilder, ValueBuilder, Arena};
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
  /// l.insert_at_height_with_builders::<(), ()>(height, kb, vb)
  /// .unwrap();
  /// ```
  #[inline]
  fn insert_at_height_with_builders<'a, KE, VE>(
    &'a self,
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
      .insert_at_height_with_builders(MIN_VERSION, height, key_builder, value_builder)
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
  /// use skl::{generic::{unique::{sync::SkipMap, Map}, Builder}, KeyBuilder, ValueBuilder};
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
  /// l.get_or_insert_with_builders::<(), ()>(kb, vb)
  /// .unwrap();
  /// ```
  #[inline]
  fn get_or_insert_with_builders<'a, KE, VE>(
    &'a self,
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
    self.get_or_insert_at_height_with_builders(self.random_height(), key_builder, value_builder)
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
  /// use skl::{generic::{unique::{sync::SkipMap, Map}, Builder}, KeyBuilder, ValueBuilder, Arena};
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
  /// l.get_or_insert_at_height_with_builders::<(), ()>(height, kb, vb)
  /// .unwrap();
  /// ```
  #[inline]
  fn get_or_insert_at_height_with_builders<'a, KE, VE>(
    &'a self,
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
    self.as_ref().get_or_insert_at_height_with_builders(
      MIN_VERSION,
      height,
      key_builder,
      value_builder,
    )
  }

  /// Removes the key-value pair if it exists. A CAS operation will be used to ensure the operation is atomic.
  ///
  /// Unlike [`get_or_remove`](Map::get_or_remove), this method will remove the value if the key already exists.
  ///
  /// - Returns `Ok(None)`:
  ///   - if the remove operation is successful or the key is marked in remove status by other threads.
  /// - Returns `Ok(Some(current))` if the key exists and not in remove status
  ///   or the entry is not successfully removed because of an update on this entry happens in another thread.
  #[inline]
  fn remove<'a, 'b: 'a>(
    &'a self,
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
    self.remove_at_height(self.random_height(), key)
  }

  /// Removes the key-value pair if it exists. A CAS operation will be used to ensure the operation is atomic.
  ///
  /// Unlike [`get_or_remove_at_height`](Map::get_or_remove_at_height), this method will remove the value if the key already exists.
  ///
  /// - Returns `Ok(None)`:
  ///   - if the remove operation is successful or the key is marked in remove status by other threads.
  /// - Returns `Ok(Some(current))` if the key exists and not in remove status
  ///   or the entry is not successfully removed because of an update on this entry happens in another thread.
  #[inline]
  #[allow(single_use_lifetimes)]
  fn remove_at_height<'a, 'b: 'a>(
    &'a self,
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
    self.as_ref().compare_remove_at_height(
      MIN_VERSION,
      height,
      key,
      Ordering::AcqRel,
      Ordering::Relaxed,
    )
  }

  /// Gets or removes the key-value pair if it exists.
  ///
  /// Unlike [`remove`](Map::remove), this method will not remove the value if the key already exists.
  ///
  /// - Returns `Ok(None)` if the key does not exist.
  /// - Returns `Ok(Some(old))` if the key already exists.
  #[inline]
  fn get_or_remove<'a, 'b: 'a>(
    &'a self,
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
    self.get_or_remove_at_height(self.random_height(), key)
  }

  /// Gets or removes the key-value pair if it exists.
  ///
  /// Unlike [`remove_at_height`](Map::remove_at_height), this method will not remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key does not exist.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{generic::{unique::{sync::SkipMap, Map}, Builder}, Arena};
  ///
  /// let map = Builder::new().with_capacity(1024).alloc::<SkipMap<str, str>>().unwrap();
  ///
  /// map.insert("hello", "world").unwrap();
  ///
  /// let height = map.random_height();
  /// map.get_or_remove_at_height(height, "hello").unwrap();
  /// ```
  #[allow(single_use_lifetimes)]
  #[inline]
  fn get_or_remove_at_height<'a, 'b: 'a>(
    &'a self,
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
    self
      .as_ref()
      .get_or_remove_at_height(MIN_VERSION, height, key)
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
  /// use skl::{generic::{unique::{sync::SkipMap, Map}, Builder}, KeyBuilder};
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
  /// l.get_or_remove_with_builder::<core::convert::Infallible>(kb)
  /// .unwrap();
  /// ```
  #[inline]
  fn get_or_remove_with_builder<'a, 'b: 'a, E>(
    &'a self,
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
    self.get_or_remove_at_height_with_builder(self.random_height(), key_builder)
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
  /// use skl::{generic::{unique::{sync::SkipMap, Map}, Builder}, KeyBuilder, Arena};
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
  /// l.get_or_remove_at_height_with_builder::<core::convert::Infallible>(height, kb)
  /// .unwrap();
  /// ```
  #[inline]
  fn get_or_remove_at_height_with_builder<'a, 'b: 'a, E>(
    &'a self,
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
      .get_or_remove_at_height_with_builder(MIN_VERSION, height, key_builder)
  }
}
