use super::*;

impl<T: Trailer, C: Comparator> SkipList<C, T> {
  /// Allocates a new node in the [`SkipList`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipList::link`] or [`SkipList::get_or_link`].
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::*;
  ///
  /// let map = SkipList::new().unwrap();
  ///
  /// let unlinked_node = map.allocate(0u8, b"hello", b"world").unwrap();
  /// map.link(unlinked_node).unwrap();
  ///
  /// let unlinked_node2 = map.allocate(0u8, b"hello", b"rust").unwrap();
  /// map.link(unlinked_node2).unwrap();
  ///
  /// let entry = map.get(0u8, b"hello").unwrap();
  /// assert_eq!(entry.value(), b"rust");
  /// ```
  #[inline]
  pub fn allocate<'a, 'b: 'a>(
    &'a self,
    version: impl Into<Version>,
    key: &'b [u8],
    value: &'b [u8],
    trailer: T,
  ) -> Result<UnlinkedNode<'a, T>, Error> {
    self.allocate_at_height(version, self.random_height(), key, value, trailer)
  }

  /// Allocates a new node with a given height in the [`SkipList`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipList::link`] or [`SkipList::get_or_link`].
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::*;
  ///
  /// let map = SkipList::new().unwrap();
  ///
  /// let random_height = map.random_height();
  ///
  /// let unlinked_node = map.allocate_at_height(0u8, random_height, b"hello", b"world").unwrap();
  /// map.link(unlinked_node).unwrap();
  ///
  /// let unlinked_node2 = map.allocate_at_height(0u8, random_height, b"hello", b"rust").unwrap();
  /// map.link(unlinked_node2).unwrap();
  ///
  /// let entry = map.get(0u8, b"hello").unwrap();
  /// assert_eq!(entry.value(), b"rust");
  /// ```
  pub fn allocate_at_height<'a, 'b: 'a>(
    &'a self,
    version: impl Into<Version>,
    height: Height,
    key: &'b [u8],
    value: &'b [u8],
    trailer: T,
  ) -> Result<UnlinkedNode<'a, T>, Error> {
    self.check_height_and_ro(height)?;

    let copy = |buf: &mut VacantBuffer| {
      let _ = buf.write(value);
      Ok(())
    };
    let val_len = value.len() as u32;
    let vb = ValueBuilder::new(val_len, copy);

    self
      .allocate_unlinked_node_in::<Infallible>(
        version,
        trailer,
        height.into(),
        Key::Occupied(key),
        Some(vb),
        Inserter::default(),
      )
      .map_err(|e| e.expect_right("must be map::Error"))
  }

  /// Gets an [`EntryRef`] corresponding to the key or allocates a new node in the [`SkipList`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipList::link`] or [`SkipList::get_or_link`].
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::*;
  ///
  /// let map = SkipList::<Ttl>::new().unwrap();
  ///
  /// let unlinked_node = map.get_or_allocate(Version::new(), b"hello", b"world", Ttl::new(std::time::Duration::from_secs(60))).unwrap().unwrap_left();
  /// map.link(unlinked_node).unwrap();
  ///
  /// let entry = map.get_or_allocate(Version::new(), b"hello", b"rust", Ttl::new(std::time::Duration::from_secs(60))).unwrap().unwrap_right();
  /// assert_eq!(entry.value(), b"world");
  /// ```
  #[inline]
  pub fn get_or_allocate<'a, 'b: 'a>(
    &'a self,
    version: impl Into<Version>,
    key: &'b [u8],
    value: &'b [u8],
    trailer: T,
  ) -> Result<Either<UnlinkedNode<'a, T>, EntryRef<'a, T>>, Error> {
    self.get_or_allocate_at_height(version, self.random_height(), key, value, trailer)
  }

  /// Gets an [`EntryRef`] corresponding to the key or allocates a new node in the [`SkipList`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipList::link`] or [`SkipList::get_or_link`].
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{*};
  ///
  /// let map = SkipList::<Ttl>::new().unwrap();
  ///
  /// let random_height = map.random_height();
  ///
  /// let unlinked_node = map.get_or_allocate_at_height(Version::new(), random_height, b"hello", b"world", Ttl::new(std::time::Duration::from_secs(60))).unwrap().unwrap_left();
  /// map.link(unlinked_node).unwrap();
  ///
  /// let entry = map.get_or_allocate_at_height(Version::new(), random_height, b"hello", b"rust", Ttl::new(std::time::Duration::from_secs(60))).unwrap().unwrap_right();
  /// assert_eq!(entry.value(), b"world");
  /// ```
  pub fn get_or_allocate_at_height<'a, 'b: 'a>(
    &'a self,
    version: impl Into<Version>,
    height: Height,
    key: &'b [u8],
    value: &'b [u8],
    trailer: T,
  ) -> Result<Either<UnlinkedNode<'a, T>, EntryRef<'a, T>>, Error> {
    self.check_height_and_ro(height)?;

    let copy = |buf: &mut VacantBuffer| {
      let _ = buf.write(value);
      Ok(())
    };

    let vb = ValueBuilder::new(value.len() as u32, copy);
    let height = super::random_height(self.opts.max_height());
    self
      .get_or_allocate_unlinked_node_in::<Infallible>(
        version,
        trailer,
        height.into(),
        Key::Occupied(key),
        Some(vb),
        Inserter::default(),
      )
      .map(|res| res.map_right(EntryRef))
      .map_err(|e| e.expect_right("must be map::Error"))
  }

  /// Allocates a new node in the [`SkipList`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipList::link`] or [`SkipList::get_or_link`].
  ///
  /// This method is useful when you want to insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipList, time::Ttl, ValueBuilder};
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
  /// struct PersonRef<'a> {
  ///   id: u32,
  ///   name: &'a str,
  /// }
  ///
  /// impl<'a> TryFrom<&'a [u8]> for PersonRef<'a> {
  ///   type Error = core::str::Utf8Error;
  ///
  ///   fn try_from(value: &'a [u8]) -> Result<Self, Self::Error> {
  ///     let id = u32::from_le_bytes(value[..4].try_into().unwrap());
  ///     let name = core::str::from_utf8(&value[4..])?;
  ///     Ok(PersonRef { id, name })
  ///   }
  /// }
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = SkipList::<Ttl>::new().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let node = l.allocate_with_value_builder::<core::convert::Infallible>(1.into(), b"alice", vb, Ttl::new(std::time::Duration::from_secs(60)))
  /// .unwrap();
  ///
  /// // do something else
  ///
  /// l.link(node).unwrap();
  ///
  /// let entry = l.get(1u8, b"alice").unwrap();
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 1);
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&2u32.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let node = l.allocate_with_value_builder::<core::convert::Infallible>(1.into(), b"alice", vb, Ttl::new(std::time::Duration::from_secs(60))).unwrap();
  ///
  /// // do something else
  ///
  /// l.link(node).unwrap();
  ///
  /// let entry = l.get(1u8, b"alice").unwrap();
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 2);
  /// ```
  #[inline]
  pub fn allocate_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    version: impl Into<Version>,
    trailer: T,
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<UnlinkedNode<'a, T>, Either<E, Error>> {
    self.allocate_at_height_with_value_builder(
      version,
      self.random_height(),
      key,
      value_builder,
      trailer,
    )
  }

  /// Allocates a new node in the [`SkipList`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipList::link`] or [`SkipList::get_or_link`].
  ///
  /// This method is useful when you want to insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipList, time::Ttl, ValueBuilder};
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
  /// struct PersonRef<'a> {
  ///   id: u32,
  ///   name: &'a str,
  /// }
  ///
  /// impl<'a> TryFrom<&'a [u8]> for PersonRef<'a> {
  ///   type Error = core::str::Utf8Error;
  ///
  ///   fn try_from(value: &'a [u8]) -> Result<Self, Self::Error> {
  ///     let id = u32::from_le_bytes(value[..4].try_into().unwrap());
  ///     let name = core::str::from_utf8(&value[4..])?;
  ///     Ok(PersonRef { id, name })
  ///   }
  /// }
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = SkipList::<Ttl>::new().unwrap();
  ///
  /// let random_height = l.random_height();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let node = l.allocate_at_height_with_value_builder::<core::convert::Infallible>(1.into(), random_height, b"alice", vb, Ttl::new(std::time::Duration::from_secs(60)))
  /// .unwrap();
  ///
  /// // do something else
  ///
  /// l.link(node).unwrap();
  ///
  /// let entry = l.get(1u8, b"alice").unwrap();
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 1);
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&2u32.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let node = l.allocate_at_height_with_value_builder::<core::convert::Infallible>(1.into(), random_height, b"alice", vb, Ttl::new(std::time::Duration::from_secs(60))).unwrap();
  ///
  /// // do something else
  ///
  /// l.link(node).unwrap();
  ///
  /// let entry = l.get(1u8, b"alice").unwrap();
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 2);
  /// ```
  pub fn allocate_at_height_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    version: impl Into<Version>,
    height: Height,
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<UnlinkedNode<'a, T>, Either<E, Error>> {
    self.check_height_and_ro(height).map_err(Either::Right)?;
    self.allocate_unlinked_node_in(
      version,
      trailer,
      height.into(),
      Key::Occupied(key),
      Some(value_builder),
      Inserter::default(),
    )
  }

  /// Gets an [`EntryRef`] corresponding to the key or allocates a new node in the [`SkipList`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipList::link`] or [`SkipList::get_or_link`].
  ///
  /// This method is useful when you want to insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// Allocates a new node in the [`SkipList`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipList::link`] or [`SkipList::get_or_link`].
  ///
  /// This method is useful when you want to insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipList, time::Ttl, ValueBuilder};
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
  /// struct PersonRef<'a> {
  ///   id: u32,
  ///   name: &'a str,
  /// }
  ///
  /// impl<'a> TryFrom<&'a [u8]> for PersonRef<'a> {
  ///   type Error = core::str::Utf8Error;
  ///
  ///   fn try_from(value: &'a [u8]) -> Result<Self, Self::Error> {
  ///     let id = u32::from_le_bytes(value[..4].try_into().unwrap());
  ///     let name = core::str::from_utf8(&value[4..])?;
  ///     Ok(PersonRef { id, name })
  ///   }
  /// }
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = SkipList::<Ttl>::new().unwrap();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let node = l.get_or_allocate_with_value_builder::<core::convert::Infallible>(1.into(), b"alice", vb, Ttl::new(std::time::Duration::from_secs(60)))
  /// .unwrap().unwrap_left();
  ///
  /// // do something else
  ///
  /// l.link(node).unwrap();
  ///
  /// let entry = l.get(1u8, b"alice").unwrap();
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 1);
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&2u32.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let entry = l.get_or_allocate_with_value_builder::<core::convert::Infallible>(1.into(), b"alice", vb, Ttl::new(std::time::Duration::from_secs(60))).unwrap().unwrap_right();
  ///
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 1);
  /// ```
  #[inline]
  pub fn get_or_allocate_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    version: impl Into<Version>,
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Either<UnlinkedNode<'a, T>, EntryRef<'a, T>>, Either<E, Error>> {
    self.get_or_allocate_at_height_with_value_builder(
      version,
      self.random_height(),
      key,
      value_builder,
      trailer,
    )
  }

  /// Gets an [`EntryRef`] corresponding to the key or allocates a new node in the [`SkipList`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipList::link`] or [`SkipList::get_or_link`].
  ///
  /// This method is useful when you want to insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// Allocates a new node in the [`SkipList`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipList::link`] or [`SkipList::get_or_link`].
  ///
  /// This method is useful when you want to insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipList, time::Ttl, ValueBuilder};
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
  /// struct PersonRef<'a> {
  ///   id: u32,
  ///   name: &'a str,
  /// }
  ///
  /// impl<'a> TryFrom<&'a [u8]> for PersonRef<'a> {
  ///   type Error = core::str::Utf8Error;
  ///
  ///   fn try_from(value: &'a [u8]) -> Result<Self, Self::Error> {
  ///     let id = u32::from_le_bytes(value[..4].try_into().unwrap());
  ///     let name = core::str::from_utf8(&value[4..])?;
  ///     Ok(PersonRef { id, name })
  ///   }
  /// }
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = SkipList::<Ttl>::new().unwrap();
  ///
  /// let random_height = l.random_height();
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let node = l.get_or_allocate_at_height_with_value_builder::<core::convert::Infallible>(1.into(), random_height, b"alice", vb, Ttl::new(std::time::Duration::from_secs(60)))
  /// .unwrap().unwrap_left();
  ///
  /// // do something else
  ///
  /// l.link(node).unwrap();
  ///
  /// let entry = l.get(1u8, b"alice").unwrap();
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 1);
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&2u32.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let entry = l.get_or_allocate_at_height_with_value_builder::<core::convert::Infallible>(1.into(), random_height, b"alice", vb, Ttl::new(std::time::Duration::from_secs(60))).unwrap().unwrap_right();
  ///
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 1);
  /// ```
  pub fn get_or_allocate_at_height_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    version: impl Into<Version>,
    height: Height,
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Either<UnlinkedNode<'a, T>, EntryRef<'a, T>>, Either<E, Error>> {
    self.check_height_and_ro(height).map_err(Either::Right)?;
    self
      .get_or_allocate_unlinked_node_in(
        version,
        trailer,
        height.into(),
        Key::Occupied(key),
        Some(value_builder),
        Inserter::default(),
      )
      .map(|res| res.map_right(EntryRef))
  }

  /// Allocates a new node with the given key and value size in the [`SkipList`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipList::link`] or [`SkipList::get_or_link`].
  ///
  /// This method is useful when you want to insert a key-value pair and you know the key size and value size but you do not have the key and value
  /// at this moment.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipList, time::Ttl, KeyBuilder, ValueBuilder};
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
  /// struct PersonRef<'a> {
  ///   id: u32,
  ///   name: &'a str,
  /// }
  ///
  /// impl<'a> TryFrom<&'a [u8]> for PersonRef<'a> {
  ///   type Error = core::str::Utf8Error;
  ///
  ///   fn try_from(value: &'a [u8]) -> Result<Self, Self::Error> {
  ///     let id = u32::from_le_bytes(value[..4].try_into().unwrap());
  ///     let name = core::str::from_utf8(&value[4..])?;
  ///     Ok(PersonRef { id, name })
  ///   }
  /// }
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = SkipList::new().unwrap();
  ///
  /// let kb = KeyBuilder::new(b"alice", |mut key| {
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
  /// let node = l.allocate_with::<core::convert::Infallible>(1u8, kb, vb)
  /// .unwrap();
  ///
  /// // do something else
  ///
  /// l.link(node).unwrap();
  ///
  /// let entry = l.get(1u8, b"alice").unwrap();
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 1);
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&2u32.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let node = l.allocate_with::<core::convert::Infallible>(1u8, kb, vb)
  /// .unwrap();
  ///
  /// // do something else
  ///
  /// l.link(node).unwrap();
  ///
  /// let entry = l.get(1u8, b"alice").unwrap();
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 2);
  /// ```
  pub fn allocate_with_builders<'a, E>(
    &'a self,
    version: impl Into<Version>,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<UnlinkedNode<'a, T>, Either<E, Error>> {
    self.allocate_at_height_with_builders(
      version,
      self.random_height(),
      key_builder,
      value_builder,
      trailer,
    )
  }

  /// Allocates a new node with the given key and value size in the [`SkipList`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipList::link`] or [`SkipList::get_or_link`].
  ///
  /// This method is useful when you want to insert a key-value pair and you know the key size and value size but you do not have the key and value
  /// at this moment.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipList, time::Ttl, u27};
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
  /// struct PersonRef<'a> {
  ///   id: u32,
  ///   name: &'a str,
  /// }
  ///
  /// impl<'a> TryFrom<&'a [u8]> for PersonRef<'a> {
  ///   type Error = core::str::Utf8Error;
  ///
  ///   fn try_from(value: &'a [u8]) -> Result<Self, Self::Error> {
  ///     let id = u32::from_le_bytes(value[..4].try_into().unwrap());
  ///     let name = core::str::from_utf8(&value[4..])?;
  ///     Ok(PersonRef { id, name })
  ///   }
  /// }
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = SkipList::new().unwrap();
  ///
  /// let node = l.allocate_with::<core::convert::Infallible>(1u8, 5u8.into(), |key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// }, encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// })
  /// .unwrap();
  ///
  /// // do something else
  ///
  /// l.link(node).unwrap();
  ///
  /// let entry = l.get(1u8, b"alice").unwrap();
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 1);
  ///
  /// let node = l.allocate_with::<core::convert::Infallible>(1u8, 5u8.into(), |key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// }, encoded_size as u32, |mut val| {
  ///   val.write(&2u32.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// })
  /// .unwrap();
  ///
  /// // do something else
  ///
  /// l.link(node).unwrap();
  ///
  /// let entry = l.get(1u8, b"alice").unwrap();
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 2);
  /// ```
  pub fn allocate_at_height_with_builders<'a, E>(
    &'a self,
    version: impl Into<Version>,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<UnlinkedNode<'a, T>, Either<E, Error>> {
    self.check_height_and_ro(height).map_err(Either::Right)?;

    let (key_size, key) = key_builder.into_components();
    let vk = self.fetch_vacant_key(key_size.into(), key)?;
    self.allocate_unlinked_node_in(
      version,
      trailer,
      height.into(),
      Key::Vacant(vk),
      Some(value_builder),
      Inserter::default(),
    )
  }

  /// Gets an [`EntryRef`] corresponding to the key or allocates a new node with the given key and value size in the [`SkipList`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipList::link`] or [`SkipList::get_or_link`].
  ///
  /// This method is useful when you want to insert a key-value pair and you know the key size and value size but you do not have the key and value
  /// at this moment.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipList, time::Ttl, u27, KeyBuilder, ValueBuilder};
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
  /// struct PersonRef<'a> {
  ///   id: u32,
  ///   name: &'a str,
  /// }
  ///
  /// impl<'a> TryFrom<&'a [u8]> for PersonRef<'a> {
  ///   type Error = core::str::Utf8Error;
  ///
  ///   fn try_from(value: &'a [u8]) -> Result<Self, Self::Error> {
  ///     let id = u32::from_le_bytes(value[..4].try_into().unwrap());
  ///     let name = core::str::from_utf8(&value[4..])?;
  ///     Ok(PersonRef { id, name })
  ///   }
  /// }
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = SkipList::<Ttl>::new().unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |mut key| {
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
  /// let node = l.get_or_allocate_with_builders::<core::convert::Infallible>(1.into(), kb, vb, Ttl::new(std::time::Duration::from_secs(60)))
  /// .unwrap().unwrap_left();
  ///
  /// // do something else
  ///
  /// l.link(node).unwrap();
  ///
  /// let entry = l.get(1u8, b"alice").unwrap();
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 1);
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |mut key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&2u32.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let entry = l.get_or_allocate_with_builders::<core::convert::Infallible>(1.into(), kb, vb, Ttl::new(std::time::Duration::from_secs(60)))
  /// .unwrap().unwrap_right();
  ///
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 1);
  /// ```
  pub fn get_or_allocate_with_builders<'a, E>(
    &'a self,
    version: impl Into<Version>,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Either<UnlinkedNode<'a, T>, EntryRef<'a, T>>, Either<E, Error>> {
    self.get_or_allocate_at_height_builders(
      version,
      self.random_height(),
      key_builder,
      value_builder,
      trailer,
    )
  }

  /// Gets an [`EntryRef`] corresponding to the key or allocates a new node with the given key and value size in the [`SkipList`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipList::link`] or [`SkipList::get_or_link`].
  ///
  /// This method is useful when you want to insert a key-value pair and you know the key size and value size but you do not have the key and value
  /// at this moment.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{u27, SkipList, KeyBuilder, ValueBuilder};
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
  /// struct PersonRef<'a> {
  ///   id: u32,
  ///   name: &'a str,
  /// }
  ///
  /// impl<'a> TryFrom<&'a [u8]> for PersonRef<'a> {
  ///   type Error = core::str::Utf8Error;
  ///
  ///   fn try_from(value: &'a [u8]) -> Result<Self, Self::Error> {
  ///     let id = u32::from_le_bytes(value[..4].try_into().unwrap());
  ///     let name = core::str::from_utf8(&value[4..])?;
  ///     Ok(PersonRef { id, name })
  ///   }
  /// }
  ///
  /// let alice = Person {
  ///   id: 1,
  ///   name: "Alice".to_string(),
  /// };
  ///
  /// let encoded_size = alice.encoded_size();
  ///
  /// let l = SkipList::<Ttl>::new().unwrap();
  /// let random_height = l.random_height();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |mut key| {
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
  /// let node = l.get_or_allocate_at_height_builders::<core::convert::Infallible>(1.into(), random_height, kb, vb, Ttl::new(std::time::Duration::from_secs(60)))
  /// .unwrap().unwrap_left();
  ///
  /// // do something else
  ///
  /// l.link(node).unwrap();
  ///
  /// let entry = l.get(1u8, b"alice").unwrap();
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 1);
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |mut key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let vb = ValueBuilder::new(encoded_size as u32, |mut val| {
  ///   val.write(&2u32.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// });
  ///
  /// let entry = l.get_or_allocate_at_height_builders::<core::convert::Infallible>(1.into(), random_height, kb, vb, Ttl::new(std::time::Duration::from_secs(60)))
  /// .unwrap().unwrap_right();
  ///
  /// let person = PersonRef::try_from(entry.value()).unwrap();
  /// assert_eq!(person.name, "Alice");
  /// assert_eq!(person.id, 1);
  /// ```
  pub fn get_or_allocate_at_height_builders<'a, E>(
    &'a self,
    version: impl Into<Version>,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Either<UnlinkedNode<'a, T>, EntryRef<'a, T>>, Either<E, Error>> {
    self.check_height_and_ro(height).map_err(Either::Right)?;

    let (key_size, key) = key_builder.into_components();

    let key_size = key_size.into();
    let vk = self.fetch_vacant_key(key_size, key)?;
    self
      .get_or_allocate_unlinked_node_in(
        version,
        trailer,
        height.into(),
        Key::Vacant(vk),
        Some(value_builder),
        Inserter::default(),
      )
      .map(|res| res.map_right(EntryRef))
  }

  /// Allocates a new node which is marked as removed in the [`SkipList`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipList::link`] or [`SkipList::get_or_link`].
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::*;
  ///
  /// let map = SkipList::u64<>::new().unwrap();
  ///
  /// map.insert(Version::new(), b"hello", b"world").unwrap();
  ///
  /// let unlinked_node = map.allocate_remove_entry(Version::new(), b"hello", Ttl::new(std::time::Duration::from_secs(60))).unwrap();
  ///
  /// // we can still get the hello entry, because of the node is not linked yet.
  ///
  /// let entry = map.get(Version::new(), b"hello").unwrap();
  /// assert_eq!(entry.value(), b"world");
  ///
  /// map.link(unlinked_node).unwrap();
  ///
  /// // now we cannot get the hello entry, because of the node is linked and marked as removed.
  /// let entry = map.get(Version::new(), b"hello");
  /// assert!(entry.is_none());
  /// ```
  pub fn allocate_remove_entry<'a, 'b: 'a>(
    &'a self,
    version: impl Into<Version>,
    key: &'b [u8],
    trailer: T,
  ) -> Result<UnlinkedNode<'a, T>, Error> {
    self.allocate_remove_entry_at_height(version, self.random_height(), key, trailer)
  }

  /// Allocates a new node which is marked as removed in the [`SkipList`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipList::link`] or [`SkipList::get_or_link`].
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::*;
  ///
  /// let map = SkipList::<Ttl>::new().unwrap();
  ///
  /// map.insert(Version::new(), b"hello", b"world").unwrap();
  ///
  /// let unlinked_node = map.allocate_remove_entry_at_height(Version::new(), map.random_height(), b"hello", Ttl::new(std::time::Duration::from_secs(60))).unwrap();
  ///
  /// // we can still get the hello entry, because of the node is not linked yet.
  ///
  /// let entry = map.get(Version::new(), b"hello").unwrap();
  /// assert_eq!(entry.value(), b"world");
  ///
  /// map.link(unlinked_node).unwrap();
  ///
  /// // now we cannot get the hello entry, because of the node is linked and marked as removed.
  /// let entry = map.get(Version::new(), b"hello");
  /// assert!(entry.is_none());
  /// ```
  #[inline]
  pub fn allocate_remove_entry_at_height<'a, 'b: 'a>(
    &'a self,
    version: impl Into<Version>,
    height: Height,
    key: &'b [u8],
    trailer: T,
  ) -> Result<UnlinkedNode<'a, T>, Error> {
    self.check_height_and_ro(height)?;
    self
      .allocate_unlinked_node_in::<Infallible>(
        version,
        trailer,
        height.into(),
        Key::Remove(key),
        Option::<RemoveValueBuilder<_>>::None,
        Inserter::default(),
      )
      .map_err(|e| e.expect_right("must be map::Error"))
  }

  /// Gets an [`EntryRef`] corresponding to the key or allocates a new node which is marked as removed in the [`SkipList`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipList::link`] or [`SkipList::get_or_link`].
  ///
  /// # Example
  ///
  /// - If the key is already removed, it will return `Either::Right(None)`.
  ///
  /// ```rust
  /// use skl::*;
  /// use core::sync::atomic::Ordering;
  ///
  /// let map = SkipList::<Ttl>::new().unwrap();
  ///
  /// map.insert(Version::new(), b"hello", b"world").unwrap();
  ///
  /// map.compare_remove(Version::new(), b"hello", Ordering::Relaxed, Ordering::Relaxed).unwrap();
  /// let unlinked_node = map.get_or_allocate_remove_entry(Version::new(), b"hello", Ttl::new(std::time::Duration::from_secs(60))).unwrap().unwrap_right();
  /// assert!(unlinked_node.is_none());
  /// ```
  ///
  /// - If the key is not removed, it will return `Either::Right(Some(EntryRef))`.
  ///
  /// ```rust
  /// use skl::*;
  ///
  /// let map = SkipList::<Ttl>::new().unwrap();
  ///
  /// map.insert(0u8, b"hello", b"world").unwrap();
  ///
  /// let unlinked_node = map.get_or_allocate_remove_entry(Version::new(), b"hello", Ttl::new(std::time::Duration::from_secs(60))).unwrap().unwrap_right();
  /// assert_eq!(unlinked_node.unwrap().value(), b"world");
  /// ```
  ///
  /// - If the key does not exist, it will return `Either::Left(UnlinkedNode)`.
  ///
  /// ```rust
  /// use skl::*;
  ///
  /// let map = SkipList::new().unwrap();
  ///
  /// let unlinked_node = map.get_or_allocate_remove_entry(Version::new(), b"hello", Ttl::new(std::time::Duration::from_secs(60))).unwrap().unwrap_left();
  ///
  /// assert_eq!(unlinked_node.key(), b"hello");
  /// assert!(unlinked_node.value().is_none());
  ///
  /// map.link(unlinked_node).unwrap();
  /// ```
  pub fn get_or_allocate_remove_entry<'a, 'b: 'a>(
    &'a self,
    version: impl Into<Version>,
    key: &'b [u8],
    trailer: T,
  ) -> Result<Either<UnlinkedNode<'a, T>, Option<EntryRef<'a, T>>>, Error> {
    self.get_or_allocate_remove_entry_at_height(version, self.random_height(), key, trailer)
  }

  /// Gets an [`EntryRef`] corresponding to the key or allocates a new node which is marked as removed in the [`SkipList`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipList::link`] or [`SkipList::get_or_link`].
  ///
  /// # Example
  ///
  /// - If the key is already removed, it will return `Either::Right(None)`.
  ///
  /// ```rust
  /// use skl::*;
  /// use core::sync::atomic::Ordering;
  ///
  /// let map = SkipList::new().unwrap();
  ///
  /// map.insert(0u8, b"hello", b"world").unwrap();
  ///
  /// map.compare_remove(0u8, b"hello", Ordering::Relaxed, Ordering::Relaxed).unwrap();
  /// let unlinked_node = map.get_or_allocate_remove_entry_at_height(Version::new(), map.random_height(), b"hello", Ttl::new(std::time::Duration::from_secs(60))).unwrap().unwrap_right();
  /// assert!(unlinked_node.is_none());
  /// ```
  ///
  /// - If the key is not removed, it will return `Either::Right(Some(EntryRef))`.
  ///
  /// ```rust
  /// use skl::*;
  ///
  /// let map = SkipList::new().unwrap();
  ///
  /// map.insert(0u8, b"hello", b"world").unwrap();
  ///
  /// let unlinked_node = map.get_or_allocate_remove_entry_at_height(Version::new(), map.random_height(), b"hello", Ttl::new(std::time::Duration::from_secs(60))).unwrap().unwrap_right();
  /// assert_eq!(unlinked_node.unwrap().value(), b"world");
  /// ```
  ///
  /// - If the key does not exist, it will return `Either::Left(UnlinkedNode)`.
  ///
  /// ```rust
  /// use skl::*;
  ///
  /// let map = SkipList::new().unwrap();
  ///
  /// let unlinked_node = map.get_or_allocate_remove_entry_at_height(Version::new(), map.random_height(), b"hello", Ttl::new(std::time::Duration::from_secs(60))).unwrap().unwrap_left();
  ///
  /// assert_eq!(unlinked_node.key(), b"hello");
  /// assert!(unlinked_node.value().is_none());
  ///
  /// map.link(unlinked_node).unwrap();
  /// ```
  pub fn get_or_allocate_remove_entry_at_height<'a, 'b: 'a>(
    &'a self,
    version: impl Into<Version>,
    height: Height,
    key: &'b [u8],
    trailer: T,
  ) -> Result<Either<UnlinkedNode<'a, T>, Option<EntryRef<'a, T>>>, Error> {
    self.check_height_and_ro(height)?;
    self
      .get_or_allocate_unlinked_node_in::<Infallible>(
        version,
        trailer,
        height.into(),
        Key::Remove(key),
        Option::<RemoveValueBuilder<Infallible>>::None,
        Inserter::default(),
      )
      .map(|res| {
        res.map_right(|ent| {
          if ent.is_removed() {
            None
          } else {
            Some(EntryRef(ent))
          }
        })
      })
      .map_err(|e| e.expect_right("must be map::Error"))
  }

  /// Allocates a new node which is marked as removed in the [`SkipList`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipList::link`] or [`SkipList::get_or_link`].
  ///
  /// This method is useful when you want to remove a key and you know the key size but you do not have the key
  /// at this moment.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipList, time::Ttl, u27, KeyBuilder};
  ///
  /// let map = SkipList::<Ttl>::new().unwrap();
  ///
  /// map.insert(0u8, b"hello", b"world").unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |mut key| {
  ///   key.write(b"hello").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let unlinked_node = map.allocate_remove_entry_builder::<core::convert::Infallible>(Version::new(), kb, Ttl::new(std::time::Duration::from_secs(60))).unwrap();
  ///
  /// // we can still get the hello entry, because of the node is not linked yet.
  /// let entry = map.get(0u8, b"hello").unwrap();
  ///
  /// assert_eq!(entry.value(), b"world");
  ///
  /// // do something else
  ///
  /// map.link(unlinked_node).unwrap();
  /// ```
  #[inline]
  pub fn allocate_remove_entry_builder<'a, E>(
    &'a self,
    version: impl Into<Version>,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<UnlinkedNode<'a, T>, Either<E, Error>> {
    self.allocate_remove_entry_at_height_with_builder(
      version,
      self.random_height(),
      key_builder,
      trailer,
    )
  }

  /// Allocates a new node which is marked as removed in the [`SkipList`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipList::link`] or [`SkipList::get_or_link`].
  ///
  /// This method is useful when you want to remove a key and you know the key size but you do not have the key
  /// at this moment.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::{SkipList, time::Ttl, u27, KeyBuilder};
  ///
  /// let map = SkipList::<Ttl>::new().unwrap();
  ///
  /// map.insert(0u8, b"hello", b"world").unwrap();
  ///
  /// let kb = KeyBuilder::new(5u8.into(), |mut key| {
  ///   key.write(b"hello").unwrap();
  ///   Ok(())
  /// });
  ///
  /// let unlinked_node = map.allocate_remove_entry_at_height_with_builder::<core::convert::Infallible>(Version::new(), map.random_height(), kb, Ttl::new(std::time::Duration::from_secs(60))).unwrap();
  ///
  /// // we can still get the hello entry, because of the node is not linked yet.
  /// let entry = map.get(Version::new(), b"hello").unwrap();
  ///
  /// assert_eq!(entry.value(), b"world");
  ///
  /// // do something else
  ///
  /// map.link(unlinked_node).unwrap();
  /// ```
  pub fn allocate_remove_entry_at_height_with_builder<'a, E>(
    &'a self,
    version: impl Into<Version>,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<UnlinkedNode<'a, T>, Either<E, Error>> {
    self.check_height_and_ro(height).map_err(Either::Right)?;

    let (key_size, key) = key_builder.into_components();
    let key_size = key_size.into();
    let vk = self.fetch_vacant_key(key_size, key)?;
    self.allocate_unlinked_node_in::<E>(
      version,
      trailer,
      height.into(),
      Key::RemoveVacant(vk),
      Option::<RemoveValueBuilder<_>>::None,
      Inserter::default(),
    )
  }

  /// Gets an [`EntryRef`] corresponding to the key or allocates a new node which is marked as removed in the [`SkipList`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipList::link`] or [`SkipList::get_or_link`].
  ///
  /// If the key is already removed, it will return `Either::Right(None)`.
  /// If the key is not removed, it will return `Either::Right(Some(EntryRef))`.
  /// If the key does not exist, it will return `Either::Left(UnlinkedNode)`.
  ///
  /// This method is useful when you want to remove a key and you know the key size but you do not have the key
  /// at this moment.
  ///
  /// # Example
  ///
  /// See examples in [`get_or_allocate_remove_entry`](SkipList::get_or_allocate_remove_entry) and [`allocate_remove_entry_with`](SkipList::allocate_remove_entry_with).
  #[inline]
  pub fn get_or_allocate_remove_entry_with_builder<'a, E>(
    &'a self,
    version: impl Into<Version>,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Either<UnlinkedNode<'a, T>, Option<EntryRef<'a, T>>>, Either<E, Error>> {
    self.get_or_allocate_remove_entry_at_height_with_builder(
      version,
      self.random_height(),
      key_builder,
      trailer,
    )
  }

  /// Gets an [`EntryRef`] corresponding to the key or allocates a new node which is marked as removed in the [`SkipList`] without linking it, this node is ready for insertion, and
  /// the caller can link it through [`SkipList::link`] or [`SkipList::get_or_link`].
  ///
  /// If the key is already removed, it will return `Either::Right(None)`.
  /// If the key is not removed, it will return `Either::Right(Some(EntryRef))`.
  /// If the key does not exist, it will return `Either::Left(UnlinkedNode)`.
  ///
  /// This method is useful when you want to remove a key and you know the key size but you do not have the key
  /// at this moment.
  ///
  /// # Example
  ///
  /// See examples in [`get_or_allocate_remove_entry_at_height`](SkipList::get_or_allocate_remove_entry_at_height) and [`allocate_remove_entry_at_height_with_builder`](SkipList::allocate_remove_entry_at_height_with_builder).
  pub fn get_or_allocate_remove_entry_at_height_with_builder<'a, E>(
    &'a self,
    version: impl Into<Version>,
    height: Height,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: T,
  ) -> Result<Either<UnlinkedNode<'a, T>, Option<EntryRef<'a, T>>>, Either<E, Error>> {
    self.check_height_and_ro(height).map_err(Either::Right)?;

    let (key_size, key) = key_builder.into_components();
    let key_size = key_size.into();
    let vk = self.fetch_vacant_key(key_size, key)?;

    self
      .get_or_allocate_unlinked_node_in::<E>(
        version,
        trailer,
        height.into(),
        Key::RemoveVacant(vk),
        Option::<RemoveValueBuilder<_>>::None,
        Inserter::default(),
      )
      .map(|res| {
        res.map_right(|ent| {
          if ent.is_removed() {
            None
          } else {
            Some(EntryRef(ent))
          }
        })
      })
  }

  /// Links a node into the [`SkipList`].
  ///
  /// Use this method to link a [`UnlinkedNode`] that was allocated through `allocate*` APIs.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::*;
  ///
  /// let map = SkipList::new().unwrap();
  ///
  /// let unlinked_node = map.allocate(0u8, b"hello", b"world").unwrap();
  ///
  /// // do something else
  ///
  /// map.link(unlinked_node).unwrap();
  /// ```
  pub fn link<'a>(&'a self, node: UnlinkedNode<'a, T>) -> Result<Option<EntryRef<'a, T>>, Error> {
    if self.arena.read_only() {
      return Err(Error::read_only());
    }

    let old = self.link_node_in(node, Ordering::Relaxed, Ordering::Relaxed, true);

    Ok(old.expect_left("insert must get InsertOk").and_then(|old| {
      if old.is_removed() {
        None
      } else {
        Some(EntryRef(old))
      }
    }))
  }

  /// Links a node into the [`SkipList`].
  ///
  /// Use this method to link a [`UnlinkedNode`] that was allocated through `allocate*` APIs.
  ///
  /// # Panic
  /// - If this [`SkipList`] is read-only.
  ///
  /// # Safety
  /// - The caller must ensure that the [`SkipList`] is not read-only.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::*;
  ///
  /// let map = SkipList::new().unwrap();
  ///
  /// let unlinked_node = map.allocate(0u8, b"hello", b"world").unwrap();
  ///
  /// // do something else
  ///
  /// unsafe { map.link_unchecked(unlinked_node); }
  /// ```
  pub unsafe fn link_unchecked<'a>(&'a self, node: UnlinkedNode<'a, T>) -> Option<EntryRef<'a, T>> {
    assert!(!self.arena.read_only(), "SkipList is read-only");

    let old = self.link_node_in(node, Ordering::Relaxed, Ordering::Relaxed, true);

    old.expect_left("insert must get InsertOk").and_then(|old| {
      if old.is_removed() {
        None
      } else {
        Some(EntryRef(old))
      }
    })
  }

  /// Gets an entry or links a node into the [`SkipList`].
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::*;
  ///
  /// let map = SkipList::new().unwrap();
  ///
  /// let unlinked_node = map.allocate(0u8, b"hello", b"world").unwrap();
  ///
  /// // do something else
  ///
  /// map.get_or_link(unlinked_node).unwrap();
  /// ```
  pub fn get_or_link<'a>(
    &'a self,
    node: UnlinkedNode<'a, T>,
  ) -> Result<Option<EntryRef<'a, T>>, Error> {
    if self.arena.read_only() {
      return Err(Error::read_only());
    }

    let old = self.link_node_in(node, Ordering::Relaxed, Ordering::Relaxed, false);

    Ok(old.expect_left("insert must get InsertOk").and_then(|old| {
      if old.is_removed() {
        None
      } else {
        Some(EntryRef(old))
      }
    }))
  }

  /// Gets an entry or links a node into the [`SkipList`].
  ///
  /// # Panic
  /// - If this [`SkipList`] is read-only.
  ///
  /// # Safety
  /// - The caller must ensure that the [`SkipList`] is not read-only.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::*;
  ///
  /// let map = SkipList::new().unwrap();
  ///
  /// let unlinked_node = map.allocate(Version::new(), b"hello", b"world").unwrap();
  ///
  /// // do something else
  ///
  /// unsafe { map.get_or_link_unchecked(unlinked_node); }
  /// ```
  pub unsafe fn get_or_link_unchecked<'a>(
    &'a self,
    node: UnlinkedNode<'a, T>,
  ) -> Option<EntryRef<'a, T>> {
    assert!(!self.arena.read_only(), "SkipList is read-only");

    let old = self.link_node_in(node, Ordering::Relaxed, Ordering::Relaxed, false);

    old.expect_left("insert must get InsertOk").and_then(|old| {
      if old.is_removed() {
        None
      } else {
        Some(EntryRef(old))
      }
    })
  }
}
