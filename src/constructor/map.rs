use super::*;

/// a
pub trait Map: Container {
  /// Upserts a new key-value pair if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert`](SkipMap::get_or_insert), this method will update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  fn insert<'a, 'b: 'a>(
    &'a self,
    key: &'b [u8],
    value: &'b [u8],
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Error>
  where
    Self::Comparator: Comparator;

  /// Upserts a new key-value pair at the given height if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert_at_height`](SkipMap::get_or_insert_at_height), this method will update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{sync::map::SkipMap, Options};
  ///
  /// let map = SkipMap::new(Options::new()).unwrap();
  ///
  /// let height = map.random_height();
  /// map.insert_at_height(height, b"hello", b"world").unwrap();
  /// ```
  fn insert_at_height<'a, 'b: 'a>(
    &'a self,
    height: Height,
    key: &'b [u8],
    value: &'b [u8],
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Error>
  where
    Self::Comparator: Comparator;

  /// Upserts a new key if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert_with_value_builder`](SkipMap::get_or_insert_with_value_builder), this method will update the value if the key with the given version already exists.
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
  /// use skl::{sync::map::SkipMap, ValueBuilder, Options};
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
  /// let l = SkipMap::new(Options::new()).unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// l.insert_with_value_builder::<core::convert::Infallible>(b"alice", vb)
  /// .unwrap();
  /// ```
  fn insert_with_value_builder<'a, E>(
    &'a self,
    key: &'a [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Either<E, Error>>
  where
    Self::Comparator: Comparator;

  /// Upserts a new key if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert_with_value_builder`](SkipMap::get_or_insert_with_value_builder), this method will update the value if the key with the given version already exists.
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
  /// use skl::{sync::map::SkipMap, ValueBuilder, Options};
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
  /// let l = SkipMap::new(Options::new()).unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.insert_at_height_with_value_builder::<core::convert::Infallible>(height, b"alice", vb)
  /// .unwrap();
  /// ```
  fn insert_at_height_with_value_builder<'a, E>(
    &'a self,
    height: Height,
    key: &'a [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Either<E, Error>>
  where
    Self::Comparator: Comparator;

  /// Inserts a new key-value pair if it does not yet exist.
  ///
  /// Unlike [`insert`](SkipMap::insert), this method will not update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully get_or_inserted.
  /// - Returns `Ok(Some(_))` if the key with the given version already exists.
  fn get_or_insert<'a, 'b: 'a>(
    &'a self,
    key: &'b [u8],
    value: &'b [u8],
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Error>
  where
    Self::Comparator: Comparator;

  /// Inserts a new key-value pair at height if it does not yet exist.
  ///
  /// Unlike [`insert_at_height`](SkipMap::insert_at_height), this method will not update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully get_or_inserted.
  /// - Returns `Ok(Some(_))` if the key with the given version already exists.
  fn get_or_insert_at_height<'a, 'b: 'a>(
    &'a self,
    height: Height,
    key: &'b [u8],
    value: &'b [u8],
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Error>
  where
    Self::Comparator: Comparator;

  /// Inserts a new key if it does not yet exist.
  ///
  /// Unlike [`insert_with_value_builder`](SkipMap::insert_with_value_builder), this method will not update the value if the key with the given version already exists.
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
  /// use skl::{sync::map::SkipMap, ValueBuilder, Options};
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
  /// let l = SkipMap::new(Options::new()).unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  /// l.get_or_insert_with_value_builder::<core::convert::Infallible>(b"alice", vb)
  /// .unwrap();
  /// ```
  fn get_or_insert_with_value_builder<'a, E>(
    &'a self,
    key: &'a [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Either<E, Error>>
  where
    Self::Comparator: Comparator;

  /// Inserts a new key if it does not yet exist.
  ///
  /// Unlike [`insert_at_height_with_value_builder`](SkipMap::insert_at_height_with_value_builder), this method will not update the value if the key with the given version already exists.
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
  /// use skl::{sync::map::SkipMap, ValueBuilder, Options};
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
  /// let l = SkipMap::new(Options::new()).unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.get_or_insert_at_height_with_value_builder::<core::convert::Infallible>(height, b"alice", vb)
  /// .unwrap();
  /// ```
  fn get_or_insert_at_height_with_value_builder<'a, E>(
    &'a self,
    height: Height,
    key: &'a [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Either<E, Error>>
  where
    Self::Comparator: Comparator;

  /// Upserts a new key if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert_with_builders`](SkipMap::get_or_insert_with_builders), this method will update the value if the key with the given version already exists.
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
  /// use skl::{sync::map::SkipMap, KeyBuilder, ValueBuilder, Options};
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
  /// let l = SkipMap::new(Options::new()).unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |mut key| {
  ///   key.put_slice(b"alice").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// l.insert_with_builders::<(), ()>(kb, vb)
  /// .unwrap();
  /// ```
  fn insert_with_builders<'a, KE, VE>(
    &'a self,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Among<KE, VE, Error>>
  where
    Self::Comparator: Comparator;

  /// Upserts a new key if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert_with_builders_and_trailer`](SkipMap::get_or_insert_with_builders_and_trailer), this method will update the value if the key with the given version already exists.
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
  /// use skl::{sync::map::SkipMap, KeyBuilder, ValueBuilder, Options};
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
  /// let l = SkipMap::new(Options::new()).unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |mut key| {
  ///   key.put_slice(b"alice").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.insert_at_height_with_builders::<(), ()>(height, kb, vb)
  /// .unwrap();
  /// ```
  fn insert_at_height_with_builders<'a, KE, VE>(
    &'a self,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Among<KE, VE, Error>>
  where
    Self::Comparator: Comparator;

  /// Inserts a new key if it does not yet exist.
  ///
  /// Unlike [`insert_with_builders`](SkipMap::insert_with_builders), this method will not update the value if the key with the given version already exists.
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
  /// use skl::{sync::map::SkipMap, KeyBuilder, ValueBuilder, Options};
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
  /// let l = SkipMap::new(Options::new()).unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |mut key| {
  ///   key.put_slice(b"alice").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// l.get_or_insert_with_builders::<(), ()>(kb, vb)
  /// .unwrap();
  /// ```
  fn get_or_insert_with_builders<'a, KE, VE>(
    &'a self,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Among<KE, VE, Error>>
  where
    Self::Comparator: Comparator;

  /// Inserts a new key if it does not yet exist.
  ///
  /// Unlike [`insert_at_height_with_builders`](SkipMap::insert_at_height_with_builders), this method will not update the value if the key with the given version already exists.
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
  /// use skl::{sync::map::SkipMap, KeyBuilder, ValueBuilder, Options};
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
  /// let l = SkipMap::new(Options::new()).unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |mut key| {
  ///   key.put_slice(b"alice").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.get_or_insert_at_height_with_builders::<(), ()>(height, kb, vb)
  /// .unwrap();
  /// ```
  fn get_or_insert_at_height_with_builders<'a, KE, VE>(
    &'a self,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Among<KE, VE, Error>>
  where
    Self::Comparator: Comparator;

  /// Removes the key-value pair if it exists. A CAS operation will be used to ensure the operation is atomic.
  ///
  /// Unlike [`get_or_remove`](SkipMap::get_or_remove), this method will remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)`:
  ///   - if the remove operation is successful or the key is marked in remove status by other threads.
  /// - Returns `Ok(Either::Right(current))` if the key with the given version already exists
  ///   and the entry is not successfully removed because of an update on this entry happens in another thread.
  fn compare_remove<'a>(
    &'a self,
    key: &'a [u8],
    success: Ordering,
    failure: Ordering,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Error>
  where
    Self::Comparator: Comparator;

  /// Removes the key-value pair if it exists. A CAS operation will be used to ensure the operation is atomic.
  ///
  /// Unlike [`get_or_remove_at_height`](SkipMap::get_or_remove_at_height), this method will remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)`:
  ///   - if the remove operation is successful or the key is marked in remove status by other threads.
  /// - Returns `Ok(Either::Right(current))` if the key with the given version already exists
  ///   and the entry is not successfully removed because of an update on this entry happens in another thread.
  fn compare_remove_at_height<'a>(
    &'a self,
    height: Height,
    key: &'a [u8],
    success: Ordering,
    failure: Ordering,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Error>
  where
    Self::Comparator: Comparator;

  /// Gets or removes the key-value pair if it exists.
  /// Unlike [`compare_remove`](SkipMap::compare_remove), this method will not remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key does not exist.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists.
  fn get_or_remove<'a>(
    &'a self,
    key: &'a [u8],
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Error>
  where
    Self::Comparator: Comparator;

  /// Gets or removes the key-value pair if it exists.
  /// Unlike [`compare_remove_at_height`](SkipMap::compare_remove_at_height), this method will not remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key does not exist.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{sync::map::SkipMap, Options};
  ///
  /// let map = SkipMap::new(Options::new()).unwrap();
  ///
  /// map.insert(b"hello", b"world").unwrap();
  ///
  /// let height = map.random_height();
  /// map.get_or_remove_at_height(height, b"hello").unwrap();
  /// ```
  fn get_or_remove_at_height<'a>(
    &'a self,
    height: Height,
    key: &'a [u8],
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Error>
  where
    Self::Comparator: Comparator;

  /// Gets or removes the key-value pair if it exists.
  /// Unlike [`compare_remove_with_builder_and_trailer`](SkipMap::compare_remove_with_builder_and_trailer), this method will not remove the value if the key with the given version already exists.
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
  /// use skl::{sync::map::SkipMap, KeyBuilder, Options};
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
  /// let l = SkipMap::new(Options::new()).unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |mut key| {
  ///   key.put_slice(b"alice").unwrap();
  ///   Ok(())
  /// });
  /// l.get_or_remove_with_builder::<core::convert::Infallible>(kb)
  /// .unwrap();
  /// ```
  fn get_or_remove_with_builder<'a, 'b: 'a, E>(
    &'a self,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Either<E, Error>>
  where
    Self::Comparator: Comparator;

  /// Gets or removes the key-value pair if it exists.
  /// Unlike [`compare_remove_at_height_with_builder_and_trailer`](SkipMap::compare_remove_at_height_with_builder_and_trailer), this method will not remove the value if the key with the given version already exists.
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
  /// use skl::{sync::map::SkipMap, KeyBuilder, Options};
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
  /// let l = SkipMap::new(Options::new()).unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |mut key| {
  ///   key.put_slice(b"alice").unwrap();
  ///   Ok(())
  /// });
  /// let height = l.random_height();
  /// l.get_or_remove_at_height_with_builder::<core::convert::Infallible>(height, kb)
  /// .unwrap();
  /// ```
  fn get_or_remove_at_height_with_builder<'a, 'b: 'a, E>(
    &'a self,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Either<E, Error>>
  where
    Self::Comparator: Comparator;
}

impl<T> Map for T
where
  T: Container,
  <T::Allocator as AllocatorSealed>::Trailer: Default,
{
  #[inline]
  fn insert<'a, 'b: 'a>(
    &'a self,
    key: &'b [u8],
    value: &'b [u8],
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Error>
  where
    Self::Comparator: Comparator,
  {
    self
      .as_ref()
      .insert(MIN_VERSION, key, value, Default::default())
  }

  #[inline]
  fn insert_at_height<'a, 'b: 'a>(
    &'a self,
    height: Height,
    key: &'b [u8],
    value: &'b [u8],
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Error>
  where
    Self::Comparator: Comparator,
  {
    self
      .as_ref()
      .insert_at_height(MIN_VERSION, height, key, value, Default::default())
  }

  #[inline]
  fn insert_with_value_builder<'a, E>(
    &'a self,
    key: &'a [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Either<E, Error>>
  where
    Self::Comparator: Comparator,
  {
    self.as_ref().insert_at_height_with_value_builder(
      MIN_VERSION,
      self.random_height(),
      key,
      value_builder,
      Default::default(),
    )
  }

  #[inline]
  fn insert_at_height_with_value_builder<'a, E>(
    &'a self,
    height: Height,
    key: &'a [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Either<E, Error>>
  where
    Self::Comparator: Comparator,
  {
    self.as_ref().insert_at_height_with_value_builder(
      MIN_VERSION,
      height,
      key,
      value_builder,
      Default::default(),
    )
  }

  #[inline]
  fn get_or_insert<'a, 'b: 'a>(
    &'a self,
    key: &'b [u8],
    value: &'b [u8],
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Error>
  where
    Self::Comparator: Comparator,
  {
    self.as_ref().get_or_insert_at_height(
      MIN_VERSION,
      self.random_height(),
      key,
      value,
      Default::default(),
    )
  }

  #[inline]
  fn get_or_insert_at_height<'a, 'b: 'a>(
    &'a self,
    height: Height,
    key: &'b [u8],
    value: &'b [u8],
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Error>
  where
    Self::Comparator: Comparator,
  {
    self
      .as_ref()
      .get_or_insert_at_height(MIN_VERSION, height, key, value, Default::default())
  }

  #[inline]
  fn get_or_insert_with_value_builder<'a, E>(
    &'a self,
    key: &'a [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Either<E, Error>>
  where
    Self::Comparator: Comparator,
  {
    self.get_or_insert_at_height_with_value_builder(self.random_height(), key, value_builder)
  }

  #[inline]
  fn get_or_insert_at_height_with_value_builder<'a, E>(
    &'a self,
    height: Height,
    key: &'a [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Either<E, Error>>
  where
    Self::Comparator: Comparator,
  {
    self.as_ref().get_or_insert_at_height_with_value_builder(
      MIN_VERSION,
      height,
      key,
      value_builder,
      Default::default(),
    )
  }

  #[inline]
  fn insert_with_builders<'a, KE, VE>(
    &'a self,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Among<KE, VE, Error>>
  where
    Self::Comparator: Comparator,
  {
    self.as_ref().insert_at_height_with_builders(
      MIN_VERSION,
      self.random_height(),
      key_builder,
      value_builder,
      Default::default(),
    )
  }

  #[inline]
  fn insert_at_height_with_builders<'a, KE, VE>(
    &'a self,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Among<KE, VE, Error>>
  where
    Self::Comparator: Comparator,
  {
    self.as_ref().insert_at_height_with_builders(
      MIN_VERSION,
      height,
      key_builder,
      value_builder,
      Default::default(),
    )
  }

  #[inline]
  fn get_or_insert_with_builders<'a, KE, VE>(
    &'a self,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Among<KE, VE, Error>>
  where
    Self::Comparator: Comparator,
  {
    self.as_ref().get_or_insert_at_height_with_builders(
      MIN_VERSION,
      self.random_height(),
      key_builder,
      value_builder,
      Default::default(),
    )
  }

  #[inline]
  fn get_or_insert_at_height_with_builders<'a, KE, VE>(
    &'a self,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Among<KE, VE, Error>>
  where
    Self::Comparator: Comparator,
  {
    self.as_ref().get_or_insert_at_height_with_builders(
      MIN_VERSION,
      height,
      key_builder,
      value_builder,
      Default::default(),
    )
  }

  #[inline]
  fn compare_remove<'a>(
    &'a self,
    key: &'a [u8],
    success: Ordering,
    failure: Ordering,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Error>
  where
    Self::Comparator: Comparator,
  {
    self.compare_remove_at_height(self.random_height(), key, success, failure)
  }

  #[inline]
  fn compare_remove_at_height<'a>(
    &'a self,
    height: Height,
    key: &'a [u8],
    success: Ordering,
    failure: Ordering,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Error>
  where
    Self::Comparator: Comparator,
  {
    self.as_ref().compare_remove_at_height(
      MIN_VERSION,
      height,
      key,
      Default::default(),
      success,
      failure,
    )
  }

  #[inline]
  fn get_or_remove<'a>(
    &'a self,
    key: &'a [u8],
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Error>
  where
    Self::Comparator: Comparator,
  {
    self.get_or_remove_at_height(self.random_height(), key)
  }

  #[inline]
  fn get_or_remove_at_height<'a>(
    &'a self,
    height: Height,
    key: &'a [u8],
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Error>
  where
    Self::Comparator: Comparator,
  {
    self
      .as_ref()
      .get_or_remove_at_height(MIN_VERSION, height, key, Default::default())
  }

  #[inline]
  fn get_or_remove_with_builder<'a, 'b: 'a, E>(
    &'a self,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Either<E, Error>>
  where
    Self::Comparator: Comparator,
  {
    self.as_ref().get_or_remove_at_height_with_builder(
      MIN_VERSION,
      self.random_height(),
      key_builder,
      Default::default(),
    )
  }

  #[inline]
  fn get_or_remove_at_height_with_builder<'a, 'b: 'a, E>(
    &'a self,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Either<E, Error>>
  where
    Self::Comparator: Comparator,
  {
    self.as_ref().get_or_remove_at_height_with_builder(
      MIN_VERSION,
      height,
      key_builder,
      Default::default(),
    )
  }
}
