use dbutils::{
  equivalent::Comparable,
  types::{KeyRef, MaybeStructured, Type},
};

use crate::allocator::WithoutVersion;

use super::*;

/// [`Map`] implementation for concurrent environment.
pub mod sync {
  pub use crate::sync::map::{IterAll, RangeAll, Entry, Iter, Range, SkipMap};
}

/// [`Map`] implementation for non-concurrent environment.
pub mod unsync {
  pub use crate::unsync::map::{IterAll, RangeAll, Entry, Iter, Range, SkipMap};
}

/// A fast, ARENA based `SkipMap` that supports forward and backward iteration.
///
/// - For concurrent environment, use [`sync::SkipMap`].
/// - For non-concurrent environment, use [`unsync::SkipMap`].
pub trait Map<K, V>
where
  K: ?Sized + 'static,
  V: ?Sized + 'static,
  Self: Arena<K, V>,
  <Self::Allocator as AllocatorSealed>::Node: WithoutVersion,
{
  /// Returns `true` if the key exists in the map.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{map::{unsync::SkipMap, Map},  Options};
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
  /// use skl::{map::{sync::SkipMap, Map}, Options};
  ///
  /// let map = Options::new().with_capacity(1024).alloc::<_, _, SkipMap<str, str>>().unwrap();
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
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Among<K::Error, V::Error, Error>>
  where
    K: Type + 'b,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type + 'b,
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
  /// use skl::{map::{sync::SkipMap, Map}, Options, Arena};
  ///
  /// let map = Options::new().with_capacity(1024).alloc::<str, str, SkipMap<_, _>>().unwrap();
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
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Among<K::Error, V::Error, Error>>
  where
    K: Type + 'b,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type + 'b,
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
  /// use skl::{map::{sync::SkipMap, Map}, ValueBuilder, Options};
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
  /// l.insert_with_value_builder::<core::convert::Infallible>(b"alice".as_slice(), vb)
  /// .unwrap();
  /// ```
  #[inline]
  #[allow(single_use_lifetimes)]
  fn insert_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    key: impl Into<MaybeStructured<'b, K>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Among<K::Error, E, Error>>
  where
    K: Type + 'b,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type + 'b,
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
  /// use skl::{map::{sync::SkipMap, Map}, ValueBuilder, Options, Arena};
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
  /// l.insert_at_height_with_value_builder::<core::convert::Infallible>(height, b"alice".as_slice(), vb)
  /// .unwrap();
  /// ```
  #[inline]
  #[allow(single_use_lifetimes)]
  fn insert_at_height_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
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
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Among<K::Error, V::Error, Error>>
  where
    K: Type + 'b,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type + 'b,
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
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Among<K::Error, V::Error, Error>>
  where
    K: Type + 'b,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type + 'b,
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
  /// use skl::{map::{sync::SkipMap, Map}, ValueBuilder, Options};
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
  /// l.get_or_insert_with_value_builder::<core::convert::Infallible>(b"alice".as_slice(), vb)
  /// .unwrap();
  /// ```
  #[inline]
  #[allow(single_use_lifetimes)]
  fn get_or_insert_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    key: impl Into<MaybeStructured<'b, K>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Among<K::Error, E, Error>>
  where
    K: Type + 'b,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type + 'b,
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
  /// use skl::{map::{sync::SkipMap, Map}, ValueBuilder, Options, Arena};
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
  /// l.get_or_insert_at_height_with_value_builder::<core::convert::Infallible>(height, b"alice".as_slice(), vb)
  /// .unwrap();
  /// ```
  #[inline]
  #[allow(single_use_lifetimes)]
  fn get_or_insert_at_height_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    height: Height,
    key: impl Into<MaybeStructured<'b, K>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Among<K::Error, E, Error>>
  where
    K: Type + 'b,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type + 'b,
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
  /// use skl::{map::{sync::SkipMap, Map}, KeyBuilder, ValueBuilder, Options};
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
  /// l.insert_with_builders::<(), ()>(kb, vb)
  /// .unwrap();
  /// ```
  #[inline]
  fn insert_with_builders<'a, KE, VE>(
    &'a self,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Among<KE, VE, Error>>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
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
  /// use skl::{map::{sync::SkipMap, Map}, KeyBuilder, ValueBuilder, Options, Arena};
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
  /// l.insert_at_height_with_builders::<(), ()>(height, kb, vb)
  /// .unwrap();
  /// ```
  #[inline]
  fn insert_at_height_with_builders<'a, KE, VE>(
    &'a self,
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
  /// use skl::{map::{sync::SkipMap, Map}, KeyBuilder, ValueBuilder, Options};
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
  /// l.get_or_insert_with_builders::<(), ()>(kb, vb)
  /// .unwrap();
  /// ```
  #[inline]
  fn get_or_insert_with_builders<'a, KE, VE>(
    &'a self,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Among<KE, VE, Error>>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
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
  /// use skl::{map::{sync::SkipMap, Map}, KeyBuilder, ValueBuilder, Options, Arena};
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
  /// l.get_or_insert_at_height_with_builders::<(), ()>(height, kb, vb)
  /// .unwrap();
  /// ```
  #[inline]
  fn get_or_insert_at_height_with_builders<'a, KE, VE>(
    &'a self,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Among<KE, VE, Error>>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
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
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Either<K::Error, Error>>
  where
    K: Type + 'b,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
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
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Either<K::Error, Error>>
  where
    K: Type + 'b,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
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
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Either<K::Error, Error>>
  where
    K: Type + 'b,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
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
  /// use skl::{map::{sync::SkipMap, Map}, Options, Arena};
  ///
  /// let map = Options::new().with_capacity(1024).alloc::<str, str, SkipMap<_, _>>().unwrap();
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
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Either<K::Error, Error>>
  where
    K: Type + 'b,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
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
  /// use skl::{map::{sync::SkipMap, Map}, KeyBuilder, Options};
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
  /// l.get_or_remove_with_builder::<core::convert::Infallible>(kb)
  /// .unwrap();
  /// ```
  #[inline]
  fn get_or_remove_with_builder<'a, 'b: 'a, E>(
    &'a self,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, K, V, Self::Allocator>>, Either<E, Error>>
  where
    K: Type,
    K::Ref<'a>: KeyRef<'a, K>,
    V: Type,
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
  /// use skl::{map::{sync::SkipMap, Map}, KeyBuilder, Options, Arena};
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
  /// l.get_or_remove_at_height_with_builder::<core::convert::Infallible>(height, kb)
  /// .unwrap();
  /// ```
  #[inline]
  fn get_or_remove_at_height_with_builder<'a, 'b: 'a, E>(
    &'a self,
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
      .get_or_remove_at_height_with_builder(MIN_VERSION, height, key_builder)
  }
}

impl<K, V, T> Map<K, V> for T
where
  K: ?Sized + 'static,
  V: ?Sized + 'static,
  T: Arena<K, V>,
  <T::Allocator as AllocatorSealed>::Node: WithoutVersion,
{
}
