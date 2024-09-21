use super::*;

/// a
pub trait TrailedMap: Container {
  /// Upserts a new key-value pair if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert`](SkipMap::get_or_insert), this method will update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  fn insert<'a, 'b: 'a>(
    &'a self,
    key: &'b [u8],
    value: &'b [u8],
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
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
  /// use skl::{unsync::trailed::SkipMap, Options};
  ///
  /// let map = SkipMap::<u64>::new(Options::new()).unwrap();
  ///
  /// let height = map.random_height();
  /// map.insert_at_height(height, b"hello", b"world", 10).unwrap();
  /// ```
  fn insert_at_height<'a, 'b: 'a>(
    &'a self,
    height: Height,
    key: &'b [u8],
    value: &'b [u8],
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
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
  /// use skl::{unsync::trailed::SkipMap, ValueBuilder, Options};
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
  /// let l = SkipMap::<u64>::new(Options::new()).unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// l.insert_with_value_builder::<core::convert::Infallible>(b"alice", vb, 10)
  /// .unwrap();
  /// ```
  fn insert_with_value_builder<'a, E>(
    &'a self,
    key: &'a [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Either<E, Error>>
  where
    Self::Comparator: Comparator;

  /// Upserts a new key if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert_at_height_with_value_builder`](SkipMap::get_or_insert_at_height_with_value_builder), this method will update the value if the key with the given version already exists.
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
  /// use skl::{unsync::trailed::SkipMap, ValueBuilder, Options};
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
  /// let l = SkipMap::<u64>::new(Options::new()).unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.insert_at_height_with_value_builder::<core::convert::Infallible>(height, b"alice", vb, 10)
  /// .unwrap();
  /// ```
  fn insert_at_height_with_value_builder<'a, E>(
    &'a self,
    height: Height,
    key: &'a [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
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
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
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
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
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
  /// use skl::{unsync::trailed::SkipMap, ValueBuilder, Options};
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
  /// let l = SkipMap::<u64>::new(Options::new()).unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  /// l.get_or_insert_with_value_builder::<core::convert::Infallible>(b"alice", vb, 10)
  /// .unwrap();
  /// ```
  fn get_or_insert_with_value_builder<'a, E>(
    &'a self,
    key: &'a [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
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
  /// use skl::{unsync::trailed::SkipMap, ValueBuilder, Options};
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
  /// let l = SkipMap::<u64>::new(Options::new()).unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.put_u32_le(alice.id).unwrap();
  ///   val.put_slice(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let height = l.random_height();
  /// l.get_or_insert_at_height_with_value_builder::<core::convert::Infallible>(height, b"alice", vb, 10)
  /// .unwrap();
  /// ```
  fn get_or_insert_at_height_with_value_builder<'a, E>(
    &'a self,
    height: Height,
    key: &'a [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
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
  /// use skl::{unsync::trailed::SkipMap, KeyBuilder, ValueBuilder, Options};
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
  /// let l = SkipMap::<u64>::new(Options::new()).unwrap();
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
  /// l.insert_with_builders::<(), ()>(kb, vb, 10)
  /// .unwrap();
  /// ```
  fn insert_with_builders<'a, KE, VE>(
    &'a self,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Among<KE, VE, Error>>
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
  /// use skl::{unsync::trailed::SkipMap, KeyBuilder, ValueBuilder, Options};
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
  /// let l = SkipMap::<u64>::new(Options::new()).unwrap();
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
  /// l.insert_at_height_with_builders::<(), ()>(height, kb, vb, 10)
  /// .unwrap();
  /// ```
  fn insert_at_height_with_builders<'a, KE, VE>(
    &'a self,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
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
  /// use skl::{unsync::trailed::SkipMap, KeyBuilder, ValueBuilder, Options};
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
  /// let l = SkipMap::<u64>::new(Options::new()).unwrap();
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
  /// l.get_or_insert_with_builders::<(), ()>(kb, vb, 10)
  /// .unwrap();
  /// ```
  fn get_or_insert_with_builders<'a, KE, VE>(
    &'a self,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
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
  /// use skl::{unsync::trailed::SkipMap, KeyBuilder, ValueBuilder, Options};
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
  /// let l = SkipMap::<u64>::new(Options::new()).unwrap();
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
  /// l.get_or_insert_at_height_with_builders::<(), ()>(height, kb, vb, 10)
  /// .unwrap();
  /// ```
  fn get_or_insert_at_height_with_builders<'a, KE, VE>(
    &'a self,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Among<KE, VE, Error>>
  where
    Self::Comparator: Comparator;

  /// Removes the key-value pair if it exists.
  fn remove<'a>(
    &'a self,
    key: &'a [u8],
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Error>
  where
    Self::Comparator: Comparator;

  /// Removes the key-value pair if it exists.
  fn remove_at_height<'a>(
    &'a self,
    height: Height,
    key: &'a [u8],
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Error>
  where
    Self::Comparator: Comparator;
}

impl<T> TrailedMap for T
where
  T: Container,
  <<T as List>::Allocator as AllocatorSealed>::Node: WithTrailer,
{
  #[inline]
  fn insert<'a, 'b: 'a>(
    &'a self,
    key: &'b [u8],
    value: &'b [u8],
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Error>
  where
    Self::Comparator: Comparator,
  {
    self
      .as_ref()
      .insert_at_height(MIN_VERSION, self.random_height(), key, value, trailer)
  }

  #[inline]
  fn insert_at_height<'a, 'b: 'a>(
    &'a self,
    height: Height,
    key: &'b [u8],
    value: &'b [u8],
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Error>
  where
    Self::Comparator: Comparator,
  {
    self
      .as_ref()
      .insert_at_height(MIN_VERSION, height, key, value, trailer)
  }

  #[inline]
  fn insert_with_value_builder<'a, E>(
    &'a self,
    key: &'a [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Either<E, Error>>
  where
    Self::Comparator: Comparator,
  {
    self.as_ref().insert_at_height_with_value_builder(
      MIN_VERSION,
      self.random_height(),
      key,
      value_builder,
      trailer,
    )
  }

  #[inline]
  fn insert_at_height_with_value_builder<'a, E>(
    &'a self,
    height: Height,
    key: &'a [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Either<E, Error>>
  where
    Self::Comparator: Comparator,
  {
    self.as_ref().insert_at_height_with_value_builder(
      MIN_VERSION,
      height,
      key,
      value_builder,
      trailer,
    )
  }

  #[inline]
  fn get_or_insert<'a, 'b: 'a>(
    &'a self,
    key: &'b [u8],
    value: &'b [u8],
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Error>
  where
    Self::Comparator: Comparator,
  {
    self
      .as_ref()
      .get_or_insert_at_height(MIN_VERSION, self.random_height(), key, value, trailer)
  }

  #[inline]
  fn get_or_insert_at_height<'a, 'b: 'a>(
    &'a self,
    height: Height,
    key: &'b [u8],
    value: &'b [u8],
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Error>
  where
    Self::Comparator: Comparator,
  {
    self
      .as_ref()
      .get_or_insert_at_height(MIN_VERSION, height, key, value, trailer)
  }

  #[inline]
  fn get_or_insert_with_value_builder<'a, E>(
    &'a self,
    key: &'a [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Either<E, Error>>
  where
    Self::Comparator: Comparator,
  {
    self.as_ref().get_or_insert_at_height_with_value_builder(
      MIN_VERSION,
      self.random_height(),
      key,
      value_builder,
      trailer,
    )
  }

  #[inline]
  fn get_or_insert_at_height_with_value_builder<'a, E>(
    &'a self,
    height: Height,
    key: &'a [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Either<E, Error>>
  where
    Self::Comparator: Comparator,
  {
    self.as_ref().get_or_insert_at_height_with_value_builder(
      MIN_VERSION,
      height,
      key,
      value_builder,
      trailer,
    )
  }

  #[inline]
  fn insert_with_builders<'a, KE, VE>(
    &'a self,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Among<KE, VE, Error>>
  where
    Self::Comparator: Comparator,
  {
    self.as_ref().insert_at_height_with_builders(
      MIN_VERSION,
      self.random_height(),
      key_builder,
      value_builder,
      trailer,
    )
  }

  #[inline]
  fn insert_at_height_with_builders<'a, KE, VE>(
    &'a self,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Among<KE, VE, Error>>
  where
    Self::Comparator: Comparator,
  {
    self.as_ref().insert_at_height_with_builders(
      MIN_VERSION,
      height,
      key_builder,
      value_builder,
      trailer,
    )
  }

  #[inline]
  fn get_or_insert_with_builders<'a, KE, VE>(
    &'a self,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Among<KE, VE, Error>>
  where
    Self::Comparator: Comparator,
  {
    self.as_ref().get_or_insert_at_height_with_builders(
      MIN_VERSION,
      self.random_height(),
      key_builder,
      value_builder,
      trailer,
    )
  }

  #[inline]
  fn get_or_insert_at_height_with_builders<'a, KE, VE>(
    &'a self,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Among<KE, VE, Error>>
  where
    Self::Comparator: Comparator,
  {
    self.as_ref().get_or_insert_at_height_with_builders(
      MIN_VERSION,
      height,
      key_builder,
      value_builder,
      trailer,
    )
  }

  #[inline]
  fn remove<'a>(
    &'a self,
    key: &'a [u8],
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Error>
  where
    Self::Comparator: Comparator,
  {
    self.as_ref().compare_remove_at_height(
      MIN_VERSION,
      self.random_height(),
      key,
      trailer,
      Ordering::Relaxed,
      Ordering::Relaxed,
    )
  }

  #[inline]
  fn remove_at_height<'a>(
    &'a self,
    height: Height,
    key: &'a [u8],
    trailer: <<Self as List>::Allocator as AllocatorSealed>::Trailer,
  ) -> Result<Option<EntryRef<'a, <Self as List>::Allocator>>, Error>
  where
    Self::Comparator: Comparator,
  {
    self.as_ref().compare_remove_at_height(
      MIN_VERSION,
      height,
      key,
      trailer,
      Ordering::Relaxed,
      Ordering::Relaxed,
    )
  }
}
