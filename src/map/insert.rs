use super::*;

impl<T: Trailer, C: Comparator> SkipMap<T, C> {
  /// Inserts a new key-value pair if it does not yet exist.
  /// Unlike [`upsert`](SkipMap::upsert), this method will not update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully get_or_inserted.
  /// - Returns `Ok(Some(_))` if the key with the given version already exists.
  pub fn get_or_insert<'a, 'b: 'a>(
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
      .update::<Infallible>(trailer, key, val_len, copy, &mut Inserter::default(), false)
      .map_err(|e| e.expect_right("must be map::Error"))
  }

  /// Inserts a new key if it does not yet exist.
  /// Unlike [`upsert_with`](SkipMap::upsert_with), this method will not update the value if the key with the given version already exists.
  ///
  /// This method is useful when you want to get_or_insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// A placeholder value will be get_or_inserted first, then you will get an [`OccupiedValue`],
  /// and you must fully fill the value with bytes later in the closure.
  ///
  /// - Returns `Ok(None)` if the key was successfully get_or_inserted.
  /// - Returns `Ok(Some(_))` if the key with the given version already exists.
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
  /// l.get_or_insert_with::<core::convert::Infallible>(1, b"alice", encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// })
  /// .unwrap();
  /// ```
  pub fn get_or_insert_with<'a, 'b: 'a, E>(
    &'a self,
    trailer: T,
    key: &'b [u8],
    value_size: u32,
    f: impl FnOnce(OccupiedValue<'a>) -> Result<(), E> + Copy,
  ) -> Result<Option<EntryRef<'a, T, C>>, Either<E, Error>> {
    if self.ro {
      return Err(Either::Right(Error::Readonly));
    }

    self.update(trailer, key, value_size, f, &mut Inserter::default(), false)
  }
}
