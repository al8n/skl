// use core::borrow::Borrow;

// use dbutils::equivalent::Comparable;

// use crate::{Arena, MIN_VERSION, GenericEntryRef};

// use super::*;

// /// The `Container` trait provides a set of read methods for interacting with the map.
// pub trait GenericContainer<K, V>
// where
//   K: ?Sized + Type,
//   V: ?Sized + Type,
//   Self: Arena<Comparator = GenericComparator<K>>,
// {
//   /// Returns `true` if the key exists in the map.
//   ///
//   /// ## Example
//   ///
//   /// ```rust
//   /// use skl::{trailed::{unsync::SkipMap, TrailedMap}, Container, Options};
//   ///
//   /// let map = Options::new().with_capacity(1024).alloc::<SkipMap::<u64>>().unwrap();
//   ///
//   /// map.insert(b"hello", b"world", 10).unwrap();
//   ///
//   /// map.remove(b"hello", 10).unwrap();
//   ///
//   /// assert!(!map.contains_key(b"hello"));
//   /// ```
//   #[inline]
//   fn contains_key<'a, Q>(&self, key: &[u8]) -> bool
//   where
//     K: Type,
//     for<'b> K::Ref<'b>: KeyRef<'b, K>,
//     Q: ?Sized + Ord + Comparable<K::Ref<'a>>,
//   {
//     self.as_ref().contains_key(MIN_VERSION, key)
//   }

//   /// Returns the first entry in the map.
//   #[inline]
//   fn first<'a>(&'a self) -> Option<GenericEntryRef<'a, K, V, Self::Allocator>>
//   where
//     K: 'static,
//     for<'b> K::Ref<'b>: KeyRef<'b, K>,
//   {
//     self.as_ref().first(MIN_VERSION).map(GenericEntryRef::from_entry)
//   }

//   /// Returns the last entry in the map.
//   #[inline]
//   fn last(&self) -> Option<GenericEntryRef<'_, K, V, Self::Allocator>>
//   where
//     K: 'static,
//     for<'b> K::Ref<'b>: KeyRef<'b, K>,
//   {
//     self.as_ref().last(MIN_VERSION).map(GenericEntryRef::from_entry)
//   }

//   // /// Returns the value associated with the given key, if it exists.
//   // ///
//   // /// ## Example
//   // ///
//   // /// ```rust
//   // /// use skl::{trailed::{sync::SkipMap, TrailedMap}, Container, Options};
//   // ///
//   // /// let map = Options::new().with_capacity(1024).alloc::<SkipMap<u64>>().unwrap();
//   // ///
//   // /// map.insert(b"hello", b"world", 10).unwrap();
//   // ///
//   // /// let ent = map.get(b"hello").unwrap();
//   // /// assert_eq!(ent.value(), b"world");
//   // ///
//   // /// map.remove(b"hello", 10).unwrap();
//   // ///
//   // /// assert!(map.get(b"hello").is_none());
//   // /// ```
//   // #[inline]
//   // fn get(&self, key: &[u8]) -> Option<EntryRef<'_, Self::Allocator>> {
//   //   self.as_ref().get(MIN_VERSION, key)
//   // }

//   // /// Returns an `EntryRef` pointing to the highest element whose key is below the given bound.
//   // /// If no such element is found then `None` is returned.
//   // #[inline]
//   // fn upper_bound(&self, upper: Bound<&[u8]>) -> Option<EntryRef<'_, Self::Allocator>> {
//   //   self.as_ref().upper_bound(MIN_VERSION, upper)
//   // }

//   // /// Returns an `EntryRef` pointing to the lowest element whose key is above the given bound.
//   // /// If no such element is found then `None` is returned.
//   // #[inline]
//   // fn lower_bound(&self, lower: Bound<&[u8]>) -> Option<EntryRef<'_, Self::Allocator>> {
//   //   self.as_ref().lower_bound(MIN_VERSION, lower)
//   // }

//   // /// Returns a new iterator, this iterator will yield the latest version of all entries in the map less or equal to the given version.
//   // #[inline]
//   // fn iter(&self) -> Iter<'_, Self::Allocator, Self::Comparator> {
//   //   self.as_ref().iter(MIN_VERSION)
//   // }

//   // /// Returns a iterator that within the range, this iterator will yield the latest version of all entries in the range less or equal to the given version.
//   // #[inline]
//   // fn range<'a, Q, R>(&'a self, range: R) -> Iter<'a, Self::Allocator, Self::Comparator, Q, R>
//   // where
//   //   Q: ?Sized + Borrow<[u8]>,
//   //   R: RangeBounds<Q> + 'a,
//   // {
//   //   self.as_ref().range(MIN_VERSION, range)
//   // }
// }

// impl<K, V, T> GenericContainer<K, V> for T
// where
//   K: ?Sized,
//   V: ?Sized,
//   T: Arena<Comparator = GenericComparator<K>>,
// {
// }
