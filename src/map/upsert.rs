use super::*;

impl<T: Trailer, C: Comparator> SkipMap<T, C> {
  /// Upserts a new key-value pair if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`insert`](SkipMap::insert), this method will update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  ///
  /// # Warning
  /// - `insert` cannot handle ABA problem if the key with the given version already exists.
  /// - `insert` can only update the value if the key with the given version already exists, trailer will not be updated.
  pub fn insert<'a, 'b: 'a>(
    &'a self,
    trailer: T,
    key: &'b [u8],
    value: &'b [u8],
  ) -> Result<Option<EntryRef<'a, T, C>>, Error> {
    if self.ro {
      return Err(Error::Readonly);
    }

    let copy = |mut buf: OccupiedValue| {
      let _ = buf.write(value);
      Ok(())
    };
    let val_len = value.len() as u32;

    self
      .update::<Infallible>(trailer, key, val_len, copy, &mut Inserter::default(), true)
      .map_err(|e| e.expect_right("must be map::Error"))
  }

  /// Upserts a new key if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`insert_with`](SkipMap::insert_with), this method will update the value if the key with the given version already exists.
  ///
  /// This method is useful when you want to insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// A placeholder value will be inserted first, then you will get an [`OccupiedValue`],
  /// and you must fully fill the value with bytes later in the closure.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  ///
  /// # Warning
  /// - `insert_with` cannot handle ABA problem if the key with the given version already exists.
  /// - `insert_with` can only update the value if the key with the given version already exists, trailer will not be updated.
  ///
  /// # Example
  ///
  /// ```rust
  /// use skl::SkipMap;
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
  /// let l = SkipMap::new(1000).unwrap();
  ///
  /// l.insert_with::<core::convert::Infallible>(1, b"alice", encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// })
  /// .unwrap();
  /// ```
  pub fn insert_with<'a, 'b: 'a, E>(
    &'a self,
    trailer: T,
    key: &'b [u8],
    value_size: u32,
    f: impl FnOnce(OccupiedValue<'a>) -> Result<(), E> + Copy,
  ) -> Result<Option<EntryRef<'a, T, C>>, Either<E, Error>> {
    if self.ro {
      return Err(Either::Right(Error::Readonly));
    }

    self.update(trailer, key, value_size, f, &mut Inserter::default(), true)
  }
}
