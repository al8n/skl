use crate::{allocator::WithVersion, Version};

use super::*;

/// [`FullMap`] implementation for concurrent environment.
pub mod sync {
  pub use crate::sync::full::SkipMap;
}

/// [`FullMap`] implementation for non-concurrent environment.
pub mod unsync {
  pub use crate::unsync::full::SkipMap;
}

/// A fast, ARENA based `SkipMap` that supports trailed structure, multiple versions, forward and backward iteration.
///
/// - For concurrent environment, use [`sync::SkipMap`].
/// - For non-concurrent environment, use [`unsync::SkipMap`].
pub trait FullMap
where
  Self: VersionedContainer,
  Self::Comparator: Comparator,
  <Self::Allocator as AllocatorSealed>::Node: WithVersion + WithTrailer,
{
  /// Upserts a new key-value pair if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert`](FullMap::get_or_insert), this method will update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  #[inline]
  fn insert<'a, 'b: 'a>(
    &'a self,
    version: Version,
    key: &'b [u8],
    value: &'b [u8],
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, Self::Allocator>>, Error> {
    self.insert_at_height(version, self.random_height(), key, value, trailer)
  }

  /// Upserts a new key-value pair at the given height if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert_at_height`](FullMap::get_or_insert_at_height), this method will update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{full::{sync::SkipMap, FullMap}, Builder, Arena};
  ///
  /// let map = Builder::new().with_capacity(1024).alloc::<SkipMap<u64>>().unwrap();
  ///
  /// let height = map.random_height();
  /// map.insert_at_height(0, height, b"hello", b"world", 10).unwrap();
  /// ```
  fn insert_at_height<'a, 'b: 'a>(
    &'a self,
    version: Version,
    height: Height,
    key: &'b [u8],
    value: &'b [u8],
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, Self::Allocator>>, Error> {
    self
      .as_ref()
      .insert_at_height(version, height, key, value, trailer)
  }

  /// Upserts a new key if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert_with_value_builder`](FullMap::get_or_insert_with_value_builder), this method will update the value if the key with the given version already exists.
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
  /// use skl::{full::{sync::SkipMap, FullMap}, ValueBuilder, Builder};
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
  /// let l = Builder::new().with_capacity(1024).alloc::<SkipMap<u64>>().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |val: &mut skl::VacantBuffer<'_>| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// l.insert_with_value_builder::<core::convert::Infallible>(1, b"alice", vb, 10)
  /// .unwrap();
  /// ```
  #[inline]
  fn insert_with_value_builder<'a, E>(
    &'a self,
    version: Version,
    key: &'a [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, Self::Allocator>>, Either<E, Error>> {
    self.insert_at_height_with_value_builder(
      version,
      self.random_height(),
      key,
      value_builder,
      trailer,
    )
  }

  /// Upserts a new key if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert_at_height_with_value_builder`](FullMap::get_or_insert_at_height_with_value_builder), this method will update the value if the key with the given version already exists.
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
  /// use skl::{full::{sync::SkipMap, FullMap}, ValueBuilder, Builder, Arena};
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
  /// let l = Builder::new().with_capacity(1024).alloc::<SkipMap<u64>>().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |val: &mut skl::VacantBuffer<'_>| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.insert_at_height_with_value_builder::<core::convert::Infallible>(1, height, b"alice", vb, 10)
  /// .unwrap();
  /// ```
  #[inline]
  fn insert_at_height_with_value_builder<'a, E>(
    &'a self,
    version: Version,
    height: Height,
    key: &'a [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, Self::Allocator>>, Either<E, Error>> {
    self
      .as_ref()
      .insert_at_height_with_value_builder(version, height, key, value_builder, trailer)
  }

  /// Inserts a new key-value pair if it does not yet exist.
  ///
  /// Unlike [`insert`](FullMap::insert), this method will not update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully get_or_inserted.
  /// - Returns `Ok(Some(_))` if the key with the given version already exists.
  #[inline]
  fn get_or_insert<'a, 'b: 'a>(
    &'a self,
    version: Version,
    key: &'b [u8],
    value: &'b [u8],
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, Self::Allocator>>, Error> {
    self.get_or_insert_at_height(version, self.random_height(), key, value, trailer)
  }

  /// Inserts a new key-value pair at height if it does not yet exist.
  ///
  /// Unlike [`insert_at_height`](FullMap::insert_at_height), this method will not update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully get_or_inserted.
  /// - Returns `Ok(Some(_))` if the key with the given version already exists.
  #[inline]
  fn get_or_insert_at_height<'a, 'b: 'a>(
    &'a self,
    version: Version,
    height: Height,
    key: &'b [u8],
    value: &'b [u8],
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, Self::Allocator>>, Error> {
    self
      .as_ref()
      .get_or_insert_at_height(version, height, key, value, trailer)
  }

  /// Inserts a new key if it does not yet exist.
  ///
  /// Unlike [`insert_with_value_builder`](FullMap::insert_with_value_builder), this method will not update the value if the key with the given version already exists.
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
  /// use skl::{full::{sync::SkipMap, FullMap}, ValueBuilder, Builder};
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
  /// let l = Builder::new().with_capacity(1024).alloc::<SkipMap<u64>>().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |val: &mut skl::VacantBuffer<'_>| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  /// l.get_or_insert_with_value_builder::<core::convert::Infallible>(1, b"alice", vb, 10)
  /// .unwrap();
  /// ```
  #[inline]
  fn get_or_insert_with_value_builder<'a, E>(
    &'a self,
    version: Version,
    key: &'a [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, Self::Allocator>>, Either<E, Error>> {
    self.get_or_insert_at_height_with_value_builder(
      version,
      self.random_height(),
      key,
      value_builder,
      trailer,
    )
  }

  /// Inserts a new key if it does not yet exist.
  ///
  /// Unlike [`insert_at_height_with_value_builder`](FullMap::insert_at_height_with_value_builder), this method will not update the value if the key with the given version already exists.
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
  /// use skl::{full::{sync::SkipMap, FullMap}, ValueBuilder, Builder, Arena};
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
  /// let l = Builder::new().with_capacity(1024).alloc::<SkipMap<u64>>().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |val: &mut skl::VacantBuffer<'_>| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.get_or_insert_at_height_with_value_builder::<core::convert::Infallible>(1, height, b"alice", vb, 10)
  /// .unwrap();
  /// ```
  #[inline]
  fn get_or_insert_at_height_with_value_builder<'a, E>(
    &'a self,
    version: Version,
    height: Height,
    key: &'a [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, Self::Allocator>>, Either<E, Error>> {
    self.as_ref().get_or_insert_at_height_with_value_builder(
      version,
      height,
      key,
      value_builder,
      trailer,
    )
  }

  /// Upserts a new key if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert_with_builders`](FullMap::get_or_insert_with_builders), this method will update the value if the key with the given version already exists.
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
  /// use skl::{full::{sync::SkipMap, FullMap}, KeyBuilder, ValueBuilder, Builder};
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
  /// let l = Builder::new().with_capacity(1024).alloc::<SkipMap<u64>>().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |key: &mut skl::VacantBuffer<'_>| {
  ///   key.put_slice(b"alice").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |val: &mut skl::VacantBuffer<'_>| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// l.insert_with_builders::<(), ()>(1, kb, vb, 10)
  /// .unwrap();
  /// ```
  #[inline]
  fn insert_with_builders<'a, KE, VE>(
    &'a self,
    version: Version,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, Self::Allocator>>, Among<KE, VE, Error>> {
    self.insert_at_height_with_builders(
      version,
      self.random_height(),
      key_builder,
      value_builder,
      trailer,
    )
  }

  /// Upserts a new key if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert_with_builders`](FullMap::get_or_insert_with_builders), this method will update the value if the key with the given version already exists.
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
  /// use skl::{full::{sync::SkipMap, FullMap}, KeyBuilder, ValueBuilder, Builder, Arena};
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
  /// let l = Builder::new().with_capacity(1024).alloc::<SkipMap<u64>>().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |key: &mut skl::VacantBuffer<'_>| {
  ///   key.put_slice(b"alice").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |val: &mut skl::VacantBuffer<'_>| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.insert_at_height_with_builders::<(), ()>(1, height, kb, vb, 10)
  /// .unwrap();
  /// ```
  #[inline]
  fn insert_at_height_with_builders<'a, KE, VE>(
    &'a self,
    version: Version,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, Self::Allocator>>, Among<KE, VE, Error>> {
    self.as_ref().insert_at_height_with_builders(
      version,
      height,
      key_builder,
      value_builder,
      trailer,
    )
  }

  /// Inserts a new key if it does not yet exist.
  ///
  /// Unlike [`insert_with_builders`](FullMap::insert_with_builders), this method will not update the value if the key with the given version already exists.
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
  /// use skl::{full::{sync::SkipMap, FullMap}, KeyBuilder, ValueBuilder, Builder};
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
  /// let l = Builder::new().with_capacity(1024).alloc::<SkipMap<u64>>().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |key: &mut skl::VacantBuffer<'_>| {
  ///   key.put_slice(b"alice").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |val: &mut skl::VacantBuffer<'_>| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// l.get_or_insert_with_builders::<(), ()>(1, kb, vb, 10)
  /// .unwrap();
  /// ```
  #[inline]
  fn get_or_insert_with_builders<'a, KE, VE>(
    &'a self,
    version: Version,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, Self::Allocator>>, Among<KE, VE, Error>> {
    self.get_or_insert_at_height_with_builders(
      version,
      self.random_height(),
      key_builder,
      value_builder,
      trailer,
    )
  }

  /// Inserts a new key if it does not yet exist.
  ///
  /// Unlike [`insert_at_height_with_builders`](FullMap::insert_at_height_with_builders), this method will not update the value if the key with the given version already exists.
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
  /// use skl::{full::{sync::SkipMap, FullMap}, KeyBuilder, ValueBuilder, Builder, Arena};
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
  /// let l = Builder::new().with_capacity(1024).alloc::<SkipMap<u64>>().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |key: &mut skl::VacantBuffer<'_>| {
  ///   key.put_slice(b"alice").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |val: &mut skl::VacantBuffer<'_>| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.get_or_insert_at_height_with_builders::<(), ()>(1, height, kb, vb, 10)
  /// .unwrap();
  /// ```
  #[inline]
  fn get_or_insert_at_height_with_builders<'a, KE, VE>(
    &'a self,
    version: Version,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, Self::Allocator>>, Among<KE, VE, Error>> {
    self.as_ref().get_or_insert_at_height_with_builders(
      version,
      height,
      key_builder,
      value_builder,
      trailer,
    )
  }

  /// Removes the key-value pair if it exists. A CAS operation will be used to ensure the operation is atomic.
  ///
  /// Unlike [`get_or_remove`](FullMap::get_or_remove), this method will remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)`:
  ///   - if the remove operation is successful or the key is marked in remove status by other threads.
  /// - Returns `Ok(Either::Right(current))` if the key with the given version already exists
  ///   and the entry is not successfully removed because of an update on this entry happens in another thread.
  #[inline]
  fn compare_remove<'a>(
    &'a self,
    version: Version,
    key: &'a [u8],
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
    success: Ordering,
    failure: Ordering,
  ) -> Result<Option<EntryRef<'a, Self::Allocator>>, Error> {
    self.compare_remove_at_height(
      version,
      self.random_height(),
      key,
      trailer,
      success,
      failure,
    )
  }

  /// Removes the key-value pair if it exists. A CAS operation will be used to ensure the operation is atomic.
  ///
  /// Unlike [`get_or_remove_at_height`](FullMap::get_or_remove_at_height), this method will remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)`:
  ///   - if the remove operation is successful or the key is marked in remove status by other threads.
  /// - Returns `Ok(Either::Right(current))` if the key with the given version already exists
  ///   and the entry is not successfully removed because of an update on this entry happens in another thread.
  #[inline]
  fn compare_remove_at_height<'a>(
    &'a self,
    version: Version,
    height: Height,
    key: &'a [u8],
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
    success: Ordering,
    failure: Ordering,
  ) -> Result<Option<EntryRef<'a, Self::Allocator>>, Error> {
    self
      .as_ref()
      .compare_remove_at_height(version, height, key, trailer, success, failure)
  }

  /// Gets or removes the key-value pair if it exists.
  /// Unlike [`compare_remove`](FullMap::compare_remove), this method will not remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key does not exist.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists.
  #[inline]
  fn get_or_remove<'a>(
    &'a self,
    version: Version,
    key: &'a [u8],
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, Self::Allocator>>, Error> {
    self.get_or_remove_at_height(version, self.random_height(), key, trailer)
  }

  /// Gets or removes the key-value pair if it exists.
  /// Unlike [`compare_remove_at_height`](FullMap::compare_remove_at_height), this method will not remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key does not exist.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{full::{sync::SkipMap, FullMap}, Builder, Arena};
  ///
  /// let map = Builder::new().with_capacity(1024).alloc::<SkipMap<u64>>().unwrap();
  ///
  /// map.insert(0, b"hello", b"world", 10).unwrap();
  ///
  /// let height = map.random_height();
  /// map.get_or_remove_at_height(0, height, b"hello", 10).unwrap();
  /// ```
  #[inline]
  fn get_or_remove_at_height<'a>(
    &'a self,
    version: Version,
    height: Height,
    key: &'a [u8],
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, Self::Allocator>>, Error> {
    self
      .as_ref()
      .get_or_remove_at_height(version, height, key, trailer)
  }

  /// Gets or removes the key-value pair if it exists.
  /// Unlike [`compare_remove`](FullMap::compare_remove), this method will not remove the value if the key with the given version already exists.
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
  /// use skl::{full::{sync::SkipMap, FullMap}, KeyBuilder, Builder};
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
  /// let l = Builder::new().with_capacity(1024).alloc::<SkipMap<u64>>().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |key: &mut skl::VacantBuffer<'_>| {
  ///   key.put_slice(b"alice").unwrap();
  ///   Ok(())
  /// });
  /// l.get_or_remove_with_builder::<core::convert::Infallible>(1, kb, 10)
  /// .unwrap();
  /// ```
  #[inline]
  fn get_or_remove_with_builder<'a, 'b: 'a, E>(
    &'a self,
    version: Version,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, Self::Allocator>>, Either<E, Error>> {
    self.get_or_remove_at_height_with_builder(version, self.random_height(), key_builder, trailer)
  }

  /// Gets or removes the key-value pair if it exists.
  /// Unlike [`compare_remove_at_height`](FullMap::compare_remove_at_height), this method will not remove the value if the key with the given version already exists.
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
  /// use skl::{full::{sync::SkipMap, FullMap}, KeyBuilder, Builder, Arena};
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
  /// let l = Builder::new().with_capacity(1024).alloc::<SkipMap<u64>>().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |key: &mut skl::VacantBuffer<'_>| {
  ///   key.put_slice(b"alice").unwrap();
  ///   Ok(())
  /// });
  /// let height = l.random_height();
  /// l.get_or_remove_at_height_with_builder::<core::convert::Infallible>(1, height, kb, 10)
  /// .unwrap();
  /// ```
  #[inline]
  fn get_or_remove_at_height_with_builder<'a, 'b: 'a, E>(
    &'a self,
    version: Version,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, Self::Allocator>>, Either<E, Error>> {
    self
      .as_ref()
      .get_or_remove_at_height_with_builder(version, height, key_builder, trailer)
  }
}

impl<T> FullMap for T
where
  T: VersionedContainer,
  T::Comparator: Comparator,
  <T::Allocator as AllocatorSealed>::Node: WithVersion + WithTrailer,
{
}
