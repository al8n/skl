use super::*;

impl<C: Comparator> SkipMap<C> {
  /// Upserts a new key-value pair if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert`](SkipMap::get_or_insert), this method will update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  #[inline]
  pub fn insert<'a, 'b: 'a>(
    &'a self,
    version: u56,
    key: &'b [u8],
    value: &'b [u8],
  ) -> Result<Option<EntryRef<'a, ()>>, Error> {
    self.insert_with_trailer(version, key, value, ())
  }

  /// Upserts a new key-value pair at the given height if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert_at_height`](SkipMap::get_or_insert_at_height), this method will update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::SkipMap;
  ///
  /// let map = SkipMap::new().unwrap();
  ///
  /// let height = map.random_height();
  /// map.insert_at_height(u56::new(0), height, b"hello", b"world").unwrap();
  /// ```
  #[inline]
  pub fn insert_at_height<'a, 'b: 'a>(
    &'a self,
    version: u56,
    height: u5,
    key: &'b [u8],
    value: &'b [u8],
  ) -> Result<Option<EntryRef<'a, ()>>, Error> {
    self.insert_at_height_with_trailer(version, height, key, value, ())
  }

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
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipMap, ValueBuilder};
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
  /// let l = SkipMap::new().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// l.insert_with_value_builder::<core::convert::Infallible>(1.into(), b"alice", vb)
  /// .unwrap();
  /// ```
  #[inline]
  pub fn insert_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    version: u56,
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, ()>>, Either<E, Error>> {
    self.insert_at_height_with_value_builder(version, self.random_height(), key, value_builder)
  }

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
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipMap, ValueBuilder};
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
  /// let l = SkipMap::new().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.insert_at_height_with_value_builder::<core::convert::Infallible>(1.into(), height, b"alice", vb)
  /// .unwrap();
  /// ```
  pub fn insert_at_height_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    version: u56,
    height: u5,
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, ()>>, Either<E, Error>> {
    self.insert_at_height_with_value_builder_and_trailer(version, height, key, value_builder, ())
  }

  /// Inserts a new key-value pair if it does not yet exist.
  ///
  /// Unlike [`insert`](SkipMap::insert), this method will not update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully get_or_inserted.
  /// - Returns `Ok(Some(_))` if the key with the given version already exists.
  #[inline]
  pub fn get_or_insert<'a, 'b: 'a>(
    &'a self,
    version: u56,
    key: &'b [u8],
    value: &'b [u8],
  ) -> Result<Option<EntryRef<'a, ()>>, Error> {
    self.get_or_insert_at_height(version, self.random_height(), key, value)
  }

  /// Inserts a new key-value pair at height if it does not yet exist.
  ///
  /// Unlike [`insert_at_height`](SkipMap::insert_at_height), this method will not update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully get_or_inserted.
  /// - Returns `Ok(Some(_))` if the key with the given version already exists.
  pub fn get_or_insert_at_height<'a, 'b: 'a>(
    &'a self,
    version: u56,
    height: u5,
    key: &'b [u8],
    value: &'b [u8],
  ) -> Result<Option<EntryRef<'a, ()>>, Error> {
    self.get_or_insert_at_height_with_trailer(version, height, key, value, ())
  }

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
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipMap, ValueBuilder};
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
  /// let l = SkipMap::new().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  /// l.get_or_insert_with_value_builder::<core::convert::Infallible>(1.into(), b"alice", vb)
  /// .unwrap();
  /// ```
  #[inline]
  pub fn get_or_insert_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    version: u56,
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, ()>>, Either<E, Error>> {
    self.get_or_insert_at_height_with_value_builder(
      version,
      self.random_height(),
      key,
      value_builder,
    )
  }

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
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipMap, ValueBuilder};
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
  /// let l = SkipMap::new().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.get_or_insert_at_height_with_value_builder::<core::convert::Infallible>(1.into(), height, b"alice", vb)
  /// .unwrap();
  /// ```
  #[inline]
  pub fn get_or_insert_at_height_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    version: u56,
    height: u5,
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, ()>>, Either<E, Error>> {
    self.get_or_insert_at_height_with_value_builder_and_trailer(
      version,
      height,
      key,
      value_builder,
      (),
    )
  }

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
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipMap, u27, KeyBuilder, ValueBuilder};
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
  /// let l = SkipMap::new().unwrap();
  ///
  /// let kb = KeyBuilder::new(u27::new(5), |mut key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// l.insert_with_builders::<core::convert::Infallible>(1.into(), kb, vb)
  /// .unwrap();
  /// ```
  #[inline]
  pub fn insert_with_builders<'a, E>(
    &'a self,
    version: u56,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, ()>>, Either<E, Error>> {
    self.insert_at_height_with_builders(version, self.random_height(), key_builder, value_builder)
  }

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
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipMap, u27, KeyBuilder, ValueBuilder};
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
  /// let l = SkipMap::new().unwrap();
  ///
  /// let kb = KeyBuilder::new(u27::new(5), |mut key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.insert_at_height_with_builders::<core::convert::Infallible>(1.into(), height, kb, vb)
  /// .unwrap();
  /// ```
  #[inline]
  pub fn insert_at_height_with_builders<'a, E>(
    &'a self,
    version: u56,
    height: u5,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, ()>>, Either<E, Error>> {
    self.insert_at_height_with_builders_and_trailer(version, height, key_builder, value_builder, ())
  }

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
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipMap, u27, KeyBuilder, ValueBuilder};
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
  /// let l = SkipMap::new().unwrap();
  ///
  /// let kb = KeyBuilder::new(u27::new(5), |mut key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// l.get_or_insert_with_builders::<core::convert::Infallible>(1.into(), kb, vb)
  /// .unwrap();
  /// ```
  #[inline]
  pub fn get_or_insert_with_builders<'a, E>(
    &'a self,
    version: u56,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, ()>>, Either<E, Error>> {
    self.get_or_insert_at_height_with_builders_and_trailer(
      version,
      self.random_height(),
      key_builder,
      value_builder,
      (),
    )
  }

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
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipMap, u27, KeyBuilder, ValueBuilder};
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
  /// let l = SkipMap::new().unwrap();
  ///
  /// let kb = KeyBuilder::new(u27::new(5), |mut key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.get_or_insert_at_height_with_builders::<core::convert::Infallible>(1.into(), height, kb, vb)
  /// .unwrap();
  /// ```
  pub fn get_or_insert_at_height_with_builders<'a, E>(
    &'a self,
    version: u56,
    height: u5,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, ()>>, Either<E, Error>> {
    self.get_or_insert_at_height_with_builders_and_trailer(
      version,
      height,
      key_builder,
      value_builder,
      (),
    )
  }

  /// Removes the key-value pair if it exists. A CAS operation will be used to ensure the operation is atomic.
  ///
  /// Unlike [`get_or_remove`](SkipMap::get_or_remove), this method will remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)`:
  ///   - if the remove operation is successful or the key is marked in remove status by other threads.
  /// - Returns `Ok(Either::Right(current))` if the key with the given version already exists
  ///   and the entry is not successfully removed because of an update on this entry happens in another thread.
  #[inline]
  pub fn compare_remove<'a, 'b: 'a>(
    &'a self,
    version: u56,
    key: &'b [u8],
    success: Ordering,
    failure: Ordering,
  ) -> Result<Option<EntryRef<'a, ()>>, Error> {
    self.compare_remove_at_height(version, self.random_height(), key, success, failure)
  }

  /// Removes the key-value pair if it exists. A CAS operation will be used to ensure the operation is atomic.
  ///
  /// Unlike [`get_or_remove_at_height`](SkipMap::get_or_remove_at_height), this method will remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)`:
  ///   - if the remove operation is successful or the key is marked in remove status by other threads.
  /// - Returns `Ok(Either::Right(current))` if the key with the given version already exists
  ///   and the entry is not successfully removed because of an update on this entry happens in another thread.
  pub fn compare_remove_at_height<'a, 'b: 'a>(
    &'a self,
    version: u56,
    height: u5,
    key: &'b [u8],
    success: Ordering,
    failure: Ordering,
  ) -> Result<Option<EntryRef<'a, ()>>, Error> {
    self.compare_remove_at_height_with_trailer(version, height, key, (), success, failure)
  }

  /// Gets or removes the key-value pair if it exists.
  /// Unlike [`compare_remove`](SkipMap::compare_remove), this method will not remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key does not exist.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists.
  #[inline]
  pub fn get_or_remove<'a, 'b: 'a>(
    &'a self,
    version: u56,
    key: &'b [u8],
  ) -> Result<Option<EntryRef<'a, ()>>, Error> {
    self.get_or_remove_at_height(version, self.random_height(), key)
  }

  /// Gets or removes the key-value pair if it exists.
  /// Unlike [`compare_remove_at_height`](SkipMap::compare_remove_at_height), this method will not remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key does not exist.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::SkipMap;
  ///
  /// let map = SkipMap::new().unwrap();
  ///
  /// map.insert(0, b"hello", b"world").unwrap();
  ///
  /// let height = map.random_height();
  /// map.get_or_remove_at_height(0, height, b"hello").unwrap();
  /// ```
  #[inline]
  pub fn get_or_remove_at_height<'a, 'b: 'a>(
    &'a self,
    version: u56,
    height: u5,
    key: &'b [u8],
  ) -> Result<Option<EntryRef<'a, ()>>, Error> {
    self.get_or_remove_at_height_with_trailer(version, height, key, ())
  }

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
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipMap, u27, KeyBuilder};
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
  /// let l = SkipMap::new().unwrap();
  ///
  /// let kb = KeyBuilder::new(u27::new(5), |mut key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// });
  /// l.get_or_remove_with_builder::<core::convert::Infallible>(1.into(), kb, 100)
  /// .unwrap();
  /// ```
  pub fn get_or_remove_with_builder<'a, 'b: 'a, E>(
    &'a self,
    version: u56,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, ()>>, Either<E, Error>> {
    self.get_or_remove_at_height_with_builder(version, self.random_height(), key_builder)
  }

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
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipMap, u27, KeyBuilder};
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
  /// let l = SkipMap::new().unwrap();
  ///
  /// let kb = KeyBuilder::new(u27::new(5), |mut key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// });
  /// let height = l.random_height();
  /// l.get_or_remove_at_height_with_builder::<core::convert::Infallible>(1.into(), height, kb)
  /// .unwrap();
  /// ```
  pub fn get_or_remove_at_height_with_builder<'a, 'b: 'a, E>(
    &'a self,
    version: u56,
    height: u5,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<Option<EntryRef<'a, ()>>, Either<E, Error>> {
    self.get_or_remove_at_height_with_builder_and_trailer(version, height, key_builder, ())
  }
}

impl<T: Trailer, C: Comparator> SkipMap<C, T> {
  /// Upserts a new key-value pair if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert_with_trailer`](SkipMap::get_or_insert_with_trailer), this method will update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  #[inline]
  pub fn insert_with_trailer<'a, 'b: 'a>(
    &'a self,
    version: u56,
    key: &'b [u8],
    value: &'b [u8],
    trailer: T,
  ) -> Result<Option<EntryRef<'a, T>>, Error> {
    self.insert_at_height_with_trailer(version, self.random_height(), key, value, trailer)
  }

  /// Upserts a new key-value pair at the given height if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert_at_height_with_trailer`](SkipMap::get_or_insert_at_height_with_trailer), this method will update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::SkipMap;
  ///
  /// let map = SkipMap::<u64>::new().unwrap();
  ///
  /// let height = map.random_height();
  /// map.insert_at_height_with_trailer(u56::new(0), height, b"hello", b"world", 100).unwrap();
  /// ```
  pub fn insert_at_height_with_trailer<'a, 'b: 'a>(
    &'a self,
    version: u56,
    height: u5,
    key: &'b [u8],
    value: &'b [u8],
    trailer: T,
  ) -> Result<Option<EntryRef<'a, T>>, Error> {
    self.check_height_and_ro(height)?;

    let copy = |buf: &mut VacantBuffer| {
      let _ = buf.write(value);
      Ok(())
    };
    let val_len = value.len() as u32;

    self
      .update::<Infallible>(
        version,
        trailer,
        height.into(),
        Key::Occupied(key),
        Some(ValueBuilder::new(val_len, copy)),
        Ordering::Relaxed,
        Ordering::Relaxed,
        Inserter::default(),
        true,
      )
      .map(|old| {
        old.expect_left("insert must get InsertOk").and_then(|old| {
          if old.is_removed() {
            None
          } else {
            Some(EntryRef(old))
          }
        })
      })
      .map_err(|e| e.expect_right("must be map::Error"))
  }

  /// Upserts a new key if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert_with_value_builder_and_trailer`](SkipMap::get_or_insert_with_value_builder_and_trailer), this method will update the value if the key with the given version already exists.
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
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipMap, ValueBuilder};
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
  /// let l = SkipMap::<u64>::new().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// l.insert_with_value_builder_and_trailer::<core::convert::Infallible>(1.into(), b"alice", vb, 100)
  /// .unwrap();
  /// ```
  #[inline]
  pub fn insert_with_value_builder_and_trailer<'a, 'b: 'a, E>(
    &'a self,
    version: u56,
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, T>>, Either<E, Error>> {
    self.insert_at_height_with_value_builder_and_trailer(
      version,
      self.random_height(),
      key,
      value_builder,
      trailer,
    )
  }

  /// Upserts a new key if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert_at_height_with_value_builder_and_trailer`](SkipMap::get_or_insert_at_height_with_value_builder_and_trailer), this method will update the value if the key with the given version already exists.
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
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipMap, ValueBuilder};
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
  /// let l = SkipMap::<u64>::new().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.insert_at_height_with_value_builder_and_trailer::<core::convert::Infallible>(1.into(), height, b"alice", vb, 100)
  /// .unwrap();
  /// ```
  pub fn insert_at_height_with_value_builder_and_trailer<'a, 'b: 'a, E>(
    &'a self,
    version: u56,
    height: u5,
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, T>>, Either<E, Error>> {
    self.check_height_and_ro(height).map_err(Either::Right)?;

    self
      .update(
        version,
        trailer,
        height.into(),
        Key::Occupied(key),
        Some(value_builder),
        Ordering::Relaxed,
        Ordering::Relaxed,
        Inserter::default(),
        true,
      )
      .map(|old| {
        old.expect_left("insert must get InsertOk").and_then(|old| {
          if old.is_removed() {
            None
          } else {
            Some(EntryRef(old))
          }
        })
      })
  }

  /// Inserts a new key-value pair if it does not yet exist.
  ///
  /// Unlike [`insert_with_trailer`](SkipMap::insert_with_trailer), this method will not update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully get_or_inserted.
  /// - Returns `Ok(Some(_))` if the key with the given version already exists.
  #[inline]
  pub fn get_or_insert_with_trailer<'a, 'b: 'a>(
    &'a self,
    version: u56,
    key: &'b [u8],
    value: &'b [u8],
    trailer: T,
  ) -> Result<Option<EntryRef<'a, T>>, Error> {
    self.get_or_insert_at_height_with_trailer(version, self.random_height(), key, value, trailer)
  }

  /// Inserts a new key-value pair at height if it does not yet exist.
  ///
  /// Unlike [`insert_at_height_with_trailer`](SkipMap::insert_at_height_with_trailer), this method will not update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully get_or_inserted.
  /// - Returns `Ok(Some(_))` if the key with the given version already exists.
  pub fn get_or_insert_at_height_with_trailer<'a, 'b: 'a>(
    &'a self,
    version: u56,
    height: u5,
    key: &'b [u8],
    value: &'b [u8],
    trailer: T,
  ) -> Result<Option<EntryRef<'a, T>>, Error> {
    self.check_height_and_ro(height)?;

    let copy = |buf: &mut VacantBuffer| {
      let _ = buf.write(value);
      Ok(())
    };
    let val_len = value.len() as u32;

    self
      .update::<Infallible>(
        version,
        trailer,
        height.into(),
        Key::Occupied(key),
        Some(ValueBuilder::new(val_len, copy)),
        Ordering::Relaxed,
        Ordering::Relaxed,
        Inserter::default(),
        false,
      )
      .map(|old| {
        old.expect_left("insert must get InsertOk").and_then(|old| {
          if old.is_removed() {
            None
          } else {
            Some(EntryRef(old))
          }
        })
      })
      .map_err(|e| e.expect_right("must be map::Error"))
  }

  /// Inserts a new key if it does not yet exist.
  ///
  /// Unlike [`insert_with_value_builder_and_trailer`](SkipMap::insert_with_value_builder_and_trailer), this method will not update the value if the key with the given version already exists.
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
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipMap, ValueBuilder};
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
  /// let l = SkipMap::<u64>::new().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  /// l.get_or_insert_with_value_builder_and_trailer::<core::convert::Infallible>(1.into(), b"alice", vb, 100)
  /// .unwrap();
  /// ```
  #[inline]
  pub fn get_or_insert_with_value_builder_and_trailer<'a, 'b: 'a, E>(
    &'a self,
    version: u56,
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, T>>, Either<E, Error>> {
    self.get_or_insert_at_height_with_value_builder_and_trailer(
      version,
      self.random_height(),
      key,
      value_builder,
      trailer,
    )
  }

  /// Inserts a new key if it does not yet exist.
  ///
  /// Unlike [`insert_at_height_with_value_builder_and_trailer`](SkipMap::insert_at_height_with_value_builder_and_trailer), this method will not update the value if the key with the given version already exists.
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
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipMap, ValueBuilder};
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
  /// let l = SkipMap::<u64>::new().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.get_or_insert_at_height_with_value_builder_and_trailer::<core::convert::Infallible>(1.into(), height, b"alice", vb, 100)
  /// .unwrap();
  /// ```
  pub fn get_or_insert_at_height_with_value_builder_and_trailer<'a, 'b: 'a, E>(
    &'a self,
    version: u56,
    height: u5,
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, T>>, Either<E, Error>> {
    self.check_height_and_ro(height).map_err(Either::Right)?;

    self
      .update(
        version,
        trailer,
        height.into(),
        Key::Occupied(key),
        Some(value_builder),
        Ordering::Relaxed,
        Ordering::Relaxed,
        Inserter::default(),
        false,
      )
      .map(|old| {
        old.expect_left("insert must get InsertOk").and_then(|old| {
          if old.is_removed() {
            None
          } else {
            Some(EntryRef(old))
          }
        })
      })
  }

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
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipMap, u27, KeyBuilder, ValueBuilder};
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
  /// let l = SkipMap::new().unwrap();
  ///
  /// let kb = KeyBuilder::new(u27::new(5), |mut key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// l.insert_with_builders_and_trailer::<core::convert::Infallible>(1.into(), kb, vb, 100)
  /// .unwrap();
  /// ```
  #[inline]
  pub fn insert_with_builders_and_trailer<'a, E>(
    &'a self,
    version: u56,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, T>>, Either<E, Error>> {
    self.insert_at_height_with_builders_and_trailer(
      version,
      self.random_height(),
      key_builder,
      value_builder,
      trailer,
    )
  }

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
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipMap, u27, KeyBuilder, ValueBuilder};
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
  /// let l = SkipMap::<u64>::new().unwrap();
  ///
  /// let kb = KeyBuilder::new(u27::new(5), |mut key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.insert_at_height_with_builders_and_trailer::<core::convert::Infallible>(1.into(), height, kb, vb, 100)
  /// .unwrap();
  /// ```
  pub fn insert_at_height_with_builders_and_trailer<'a, E>(
    &'a self,
    version: u56,
    height: u5,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, T>>, Either<E, Error>> {
    self.check_height_and_ro(height).map_err(Either::Right)?;

    let (key_size, key) = key_builder.into_components();
    let vk = self.fetch_vacant_key(u32::from(key_size), key)?;

    self
      .update(
        version,
        trailer,
        height.into(),
        Key::Vacant(vk),
        Some(value_builder),
        Ordering::Relaxed,
        Ordering::Relaxed,
        Inserter::default(),
        true,
      )
      .map(|old| {
        old.expect_left("insert must get InsertOk").and_then(|old| {
          if old.is_removed() {
            None
          } else {
            Some(EntryRef(old))
          }
        })
      })
  }

  /// Inserts a new key if it does not yet exist.
  ///
  /// Unlike [`insert_with_builders_and_trailer`](SkipMap::insert_with_builders_and_trailer), this method will not update the value if the key with the given version already exists.
  ///
  /// This method is useful when you want to get_or_insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// A placeholder will be inserted first, then you will get an [`VacantBuffer`],
  /// and you must fill the buffer with bytes later in the closure.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipMap, u27, KeyBuilder, ValueBuilder};
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
  /// let l = SkipMap::<u64>::new().unwrap();
  ///
  /// let kb = KeyBuilder::new(u27::new(5), |mut key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// l.get_or_insert_with_builders_and_trailer::<core::convert::Infallible>(1.into(), kb, vb, 100)
  /// .unwrap();
  /// ```
  #[inline]
  pub fn get_or_insert_with_builders_and_trailer<'a, E>(
    &'a self,
    version: u56,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, T>>, Either<E, Error>> {
    self.get_or_insert_at_height_with_builders_and_trailer(
      version,
      self.random_height(),
      key_builder,
      value_builder,
      trailer,
    )
  }

  /// Inserts a new key if it does not yet exist.
  ///
  /// Unlike [`insert_at_height_with_builders_and_trailer`](SkipMap::insert_at_height_with_builders_and_trailer), this method will not update the value if the key with the given version already exists.
  ///
  /// This method is useful when you want to get_or_insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// A placeholder will be inserted first, then you will get an [`VacantBuffer`],
  /// and you must fill the buffer with bytes later in the closure.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipMap, u27, KeyBuilder, ValueBuilder};
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
  /// let l = SkipMap::<u64>::new().unwrap();
  ///
  /// let kb = KeyBuilder::new(u27::new(5), |mut key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.get_or_insert_at_height_with_builders_and_trailer::<core::convert::Infallible>(1.into(), height, kb, vb, 100)
  /// .unwrap();
  /// ```
  pub fn get_or_insert_at_height_with_builders_and_trailer<'a, E>(
    &'a self,
    version: u56,
    height: u5,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, T>>, Either<E, Error>> {
    if self.arena.read_only() {
      return Err(Either::Right(Error::read_only()));
    }

    let (key_size, key) = key_builder.into_components();
    let vk = self.fetch_vacant_key(u32::from(key_size), key)?;

    self
      .update(
        version,
        trailer,
        height.into(),
        Key::Vacant(vk),
        Some(value_builder),
        Ordering::Relaxed,
        Ordering::Relaxed,
        Inserter::default(),
        false,
      )
      .map(|old| {
        old.expect_left("insert must get InsertOk").and_then(|old| {
          if old.is_removed() {
            None
          } else {
            Some(EntryRef(old))
          }
        })
      })
  }

  /// Removes the key-value pair if it exists. A CAS operation will be used to ensure the operation is atomic.
  ///
  /// Unlike [`get_or_remove_with_trailer`](SkipMap::get_or_remove_with_trailer), this method will remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)`:
  ///   - if the remove operation is successful or the key is marked in remove status by other threads.
  /// - Returns `Ok(Either::Right(current))` if the key with the given version already exists
  ///   and the entry is not successfully removed because of an update on this entry happens in another thread.
  #[inline]
  pub fn compare_remove_with_trailer<'a, 'b: 'a>(
    &'a self,
    version: u56,
    key: &'b [u8],
    trailer: T,
    success: Ordering,
    failure: Ordering,
  ) -> Result<Option<EntryRef<'a, T>>, Error> {
    self.compare_remove_at_height_with_trailer(
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
  /// Unlike [`get_or_remove_at_height_with_trailer`](SkipMap::get_or_remove_at_height_with_trailer), this method will remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)`:
  ///   - if the remove operation is successful or the key is marked in remove status by other threads.
  /// - Returns `Ok(Either::Right(current))` if the key with the given version already exists
  ///   and the entry is not successfully removed because of an update on this entry happens in another thread.
  pub fn compare_remove_at_height_with_trailer<'a, 'b: 'a>(
    &'a self,
    version: u56,
    height: u5,
    key: &'b [u8],
    trailer: T,
    success: Ordering,
    failure: Ordering,
  ) -> Result<Option<EntryRef<'a, T>>, Error> {
    self.check_height_and_ro(height)?;

    self
      .update(
        version,
        trailer,
        height.into(),
        Key::Remove(key),
        Option::<RemoveValueBuilder<Infallible>>::None,
        success,
        failure,
        Inserter::default(),
        true,
      )
      .map(|res| match res {
        Either::Left(_) => None,
        Either::Right(res) => match res {
          Ok(old) => {
            if old.is_removed() {
              None
            } else {
              Some(EntryRef(old))
            }
          }
          Err(current) => {
            if current.is_removed() {
              None
            } else {
              Some(EntryRef(current))
            }
          }
        },
      })
      .map_err(|e| e.expect_right("must be map::Error"))
  }

  /// Gets or removes the key-value pair if it exists.
  /// Unlike [`compare_remove`](SkipMap::compare_remove), this method will not remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key does not exist.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists.
  #[inline]
  pub fn get_or_remove_with_trailer<'a, 'b: 'a>(
    &'a self,
    version: u56,
    key: &'b [u8],
    trailer: T,
  ) -> Result<Option<EntryRef<'a, T>>, Error> {
    self.get_or_remove_at_height_with_trailer(version, self.random_height(), key, trailer)
  }

  /// Gets or removes the key-value pair if it exists.
  /// Unlike [`compare_remove_at_height`](SkipMap::compare_remove_at_height), this method will not remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key does not exist.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::SkipMap;
  ///
  /// let map = SkipMap::<u64>::new().unwrap();
  ///
  /// map.insert(u56::new(0), b"hello", b"world").unwrap();
  ///
  /// let height = map.random_height();
  /// map.get_or_remove_at_height_with_trailer(u56::new(0), height, b"hello", 100).unwrap();
  /// ```
  pub fn get_or_remove_at_height_with_trailer<'a, 'b: 'a>(
    &'a self,
    version: u56,
    height: u5,
    key: &'b [u8],
    trailer: T,
  ) -> Result<Option<EntryRef<'a, T>>, Error> {
    self.check_height_and_ro(height)?;

    self
      .update(
        version,
        trailer,
        height.into(),
        Key::Remove(key),
        Option::<RemoveValueBuilder<Infallible>>::None,
        Ordering::Relaxed,
        Ordering::Relaxed,
        Inserter::default(),
        false,
      )
      .map(|res| match res {
        Either::Left(old) => match old {
          Some(old) => {
            if old.is_removed() {
              None
            } else {
              Some(EntryRef(old))
            }
          }
          None => None,
        },
        _ => unreachable!("get_or_remove does not use CAS, so it must return `Either::Left`"),
      })
      .map_err(|e| e.expect_right("must be map::Error"))
  }

  /// Gets or removes the key-value pair if it exists.
  /// Unlike [`compare_remove_with_trailer`](SkipMap::compare_remove_with_trailer), this method will not remove the value if the key with the given version already exists.
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
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipMap, u27, KeyBuilder};
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
  /// let l = SkipMap::<u64>::new().unwrap();
  ///
  /// let kb = KeyBuilder::new(u27::new(5), |mut key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// });
  /// l.get_or_remove_with_builder_and_trailer::<core::convert::Infallible>(1.into(), kb, 100)
  /// .unwrap();
  /// ```
  pub fn get_or_remove_with_builder_and_trailer<'a, 'b: 'a, E>(
    &'a self,
    version: u56,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, T>>, Either<E, Error>> {
    self.get_or_remove_at_height_with_builder_and_trailer(
      version,
      self.random_height(),
      key_builder,
      trailer,
    )
  }

  /// Gets or removes the key-value pair if it exists.
  /// Unlike [`compare_remove_at_height_with_trailer`](SkipMap::compare_remove_at_height_with_trailer), this method will not remove the value if the key with the given version already exists.
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
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipMap, u27, KeyBuilder};
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
  /// let l = SkipMap::<u64>::new().unwrap();
  ///
  /// let kb = KeyBuilder::new(u27::new(5), |mut key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// });
  /// let height = l.random_height();
  /// l.get_or_remove_at_height_with_builder_and_trailer::<core::convert::Infallible>(1.into(), height, kb, 100)
  /// .unwrap();
  /// ```
  pub fn get_or_remove_at_height_with_builder_and_trailer<'a, 'b: 'a, E>(
    &'a self,
    version: u56,
    height: u5,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Option<EntryRef<'a, T>>, Either<E, Error>> {
    self.check_height_and_ro(height).map_err(Either::Right)?;

    let (key_size, key) = key_builder.into_components();
    let vk = self.fetch_vacant_key(u32::from(key_size), key)?;
    let key = Key::RemoveVacant(vk);
    self
      .update(
        version,
        trailer,
        height.into(),
        key,
        Option::<RemoveValueBuilder<Infallible>>::None,
        Ordering::Relaxed,
        Ordering::Relaxed,
        Inserter::default(),
        false,
      )
      .map(|res| match res {
        Either::Left(old) => match old {
          Some(old) => {
            if old.is_removed() {
              None
            } else {
              Some(EntryRef(old))
            }
          }
          None => None,
        },
        _ => unreachable!("get_or_remove does not use CAS, so it must return `Either::Left`"),
      })
      .map_err(|e| Either::Right(e.expect_right("must be map::Error")))
  }
}
