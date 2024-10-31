use dbutils::{
  equivalent::Comparable,
  types::{KeyRef, Type},
};

use super::*;

/// The `Container` trait provides a set of read methods for interacting with the map.
pub trait Container<K, V>
where
  K: ?Sized + 'static,
  V: ?Sized + 'static,
  Self: Arena<K, V>,
{
  /// Returns `true` if the key exists in the map.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{map::{unsync::SkipMap, Map}, Container, Options};
  ///
  /// let map = Options::new().with_capacity(1024).alloc::<_, _, SkipMap::<str, str>>().unwrap();
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
    Q: ?Sized + Comparable<K::Ref<'a>>,
  {
    self.as_ref().contains_key(MIN_VERSION, key)
  }

  /// Returns the first entry in the map.
  #[inline]
  fn first<'a>(&'a self) -> Option<EntryRef<'a, K, V, Self::Allocator>>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
  {
    self.as_ref().first(MIN_VERSION)
  }

  /// Returns the last entry in the map.
  #[inline]
  fn last<'a>(&'a self) -> Option<EntryRef<'a, K, V, Self::Allocator>>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
  {
    self.as_ref().last(MIN_VERSION)
  }

  /// Returns the value associated with the given key, if it exists.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{trailed::{sync::SkipMap, TrailedMap}, Container, Options};
  ///
  /// let map = Options::new().with_capacity(1024).alloc::<_, _, SkipMap<str, str, u64>>().unwrap();
  ///
  /// map.insert("hello", "world", 10).unwrap();
  ///
  /// let ent = map.get("hello").unwrap();
  /// assert_eq!(ent.value(), "world");
  ///
  /// map.remove("hello", 10).unwrap();
  ///
  /// assert!(map.get("hello").is_none());
  /// ```
  #[inline]
  fn get<'a, Q>(&'a self, key: &Q) -> Option<EntryRef<'a, K, V, Self::Allocator>>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
    Q: ?Sized + Comparable<K::Ref<'a>>,
  {
    self.as_ref().get(MIN_VERSION, key)
  }

  /// Returns an `EntryRef` pointing to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  #[inline]
  fn upper_bound<'a, Q>(&'a self, upper: Bound<&Q>) -> Option<EntryRef<'a, K, V, Self::Allocator>>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
    Q: ?Sized + Comparable<K::Ref<'a>>,
  {
    self.as_ref().upper_bound(MIN_VERSION, upper)
  }

  /// Returns an `EntryRef` pointing to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  #[inline]
  fn lower_bound<'a, Q>(&'a self, lower: Bound<&Q>) -> Option<EntryRef<'a, K, V, Self::Allocator>>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
    Q: ?Sized + Comparable<K::Ref<'a>>,
  {
    self.as_ref().lower_bound(MIN_VERSION, lower)
  }

  /// Returns a new iterator, this iterator will yield the latest version of all entries in the map less or equal to the given version.
  #[inline]
  fn iter<'a>(&'a self) -> Iter<'a, K, V, Self::Allocator>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
  {
    self.as_ref().iter(MIN_VERSION)
  }

  /// Returns a iterator that within the range, this iterator will yield the latest version of all entries in the range less or equal to the given version.
  #[inline]
  fn range<'a, Q, R>(&'a self, range: R) -> Iter<'a, K, V, Self::Allocator, Q, R>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
    Q: ?Sized + Comparable<K::Ref<'a>>,
    R: RangeBounds<Q>,
  {
    self.as_ref().range(MIN_VERSION, range)
  }
}

impl<K, V, T> Container<K, V> for T
where
  K: ?Sized + 'static,
  V: ?Sized + 'static,
  T: Arena<K, V>,
{
}
