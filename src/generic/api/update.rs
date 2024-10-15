use core::sync::atomic::Ordering;

use among::Among;
use dbutils::{
  buffer::VacantBuffer,
  traits::{KeyRef, MaybeStructured, Type},
};
use either::Either;
use rarena_allocator::Allocator as _;

use super::{
  entry::EntryRef, Allocator, Error, Height, Inserter, Key, KeyOptions, RemoveValueOptions,
  SkipList, ValueOptions, Version,
};

impl<K, V, A> SkipList<K, V, A>
where
  K: ?Sized + Type + 'static,
  V: ?Sized + Type + 'static,
  A: Allocator,
{
  /// Upserts a new key-value pair if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert`](SkipList::get_or_insert), this method will update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  #[inline]
  pub fn insert<'a, 'b: 'a>(
    &'a self,
    version: Version,
    key: impl Into<MaybeStructured<'b, K>>,
    value: impl Into<MaybeStructured<'b, V>>,
    trailer: A::Trailer,
  ) -> Result<Option<EntryRef<'a, K, V, A>>, Among<K::Error, V::Error, Error>>
  where
    K::Ref<'a>: KeyRef<'a, K>,
  {
    self.insert_at_height(version, self.random_height(), key, value, trailer)
  }

  /// Upserts a new key-value pair at the given height if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert_at_height`](SkipList::get_or_insert_at_height), this method will update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  pub fn insert_at_height<'a, 'b: 'a>(
    &'a self,
    version: Version,
    height: Height,
    key: impl Into<MaybeStructured<'b, K>>,
    value: impl Into<MaybeStructured<'b, V>>,
    trailer: A::Trailer,
  ) -> Result<Option<EntryRef<'a, K, V, A>>, Among<K::Error, V::Error, Error>>
  where
    K::Ref<'a>: KeyRef<'a, K>,
  {
    self.check_height_and_ro(height).map_err(Among::Right)?;

    let key: MaybeStructured<'_, K> = key.into();
    let value: MaybeStructured<'_, V> = value.into();

    let copy = |buf: &mut VacantBuffer<'_>| value.encode_to_buffer(buf).map(|_| ());
    let val_len = value.encoded_len() as u32;

    self
      .update(
        version,
        trailer,
        height.into(),
        Key::from((false, key)),
        Some(ValueOptions::new(val_len, copy)),
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

  /// Upserts a new key if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`get_or_insert_at_height_with_value_builder`](SkipList::get_or_insert_at_height_with_value_builder), this method will update the value if the key with the given version already exists.
  ///
  /// This method is useful when you want to insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// A placeholder will be inserted first, then you will get an [`VacantBuffer`],
  /// and you must fill the buffer with bytes later in the closure.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  #[allow(single_use_lifetimes)]
  pub fn insert_at_height_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    version: Version,
    height: Height,
    key: impl Into<MaybeStructured<'b, K>>,
    value_builder: ValueOptions<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: A::Trailer,
  ) -> Result<Option<EntryRef<'a, K, V, A>>, Among<K::Error, E, Error>>
  where
    K::Ref<'a>: KeyRef<'a, K>,
  {
    self.check_height_and_ro(height).map_err(Either::Right)?;

    let key: MaybeStructured<'_, K> = key.into();

    self
      .update(
        version,
        trailer,
        height.into(),
        Key::from((false, key)),
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

  /// Inserts a new key-value pair at height if it does not yet exist.
  ///
  /// Unlike [`insert_at_height`](SkipList::insert_at_height), this method will not update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully get_or_inserted.
  /// - Returns `Ok(Some(_))` if the key with the given version already exists.
  pub fn get_or_insert_at_height<'a, 'b: 'a>(
    &'a self,
    version: Version,
    height: Height,
    key: impl Into<MaybeStructured<'b, K>>,
    value: impl Into<MaybeStructured<'b, V>>,
    trailer: A::Trailer,
  ) -> Result<Option<EntryRef<'a, K, V, A>>, Among<K::Error, V::Error, Error>>
  where
    K::Ref<'a>: KeyRef<'a, K>,
  {
    self.check_height_and_ro(height).map_err(Among::Right)?;

    let key: MaybeStructured<'_, K> = key.into();
    let value: MaybeStructured<'_, V> = value.into();
    let copy = |buf: &mut VacantBuffer<'_>| value.encode_to_buffer(buf).map(|_| ());
    let val_len = value.encoded_len() as u32;

    self
      .update(
        version,
        trailer,
        height.into(),
        Key::from((false, key)),
        Some(ValueOptions::new(val_len, copy)),
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

  /// Inserts a new key if it does not yet exist.
  ///
  /// Unlike [`insert_at_height_with_value_builder`](SkipList::insert_at_height_with_value_builder), this method will not update the value if the key with the given version already exists.
  ///
  /// This method is useful when you want to get_or_insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// A placeholder will be inserted first, then you will get an [`VacantBuffer`],
  /// and you must fill the buffer with bytes later in the closure.
  ///
  /// - Returns `Ok(None)` if the key was successfully get_or_inserted.
  /// - Returns `Ok(Some(_))` if the key with the given version already exists.
  #[allow(single_use_lifetimes)]
  pub fn get_or_insert_at_height_with_value_builder<'a, 'b: 'a, E>(
    &'a self,
    version: Version,
    height: Height,
    key: impl Into<MaybeStructured<'b, K>>,
    value_builder: ValueOptions<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: A::Trailer,
  ) -> Result<Option<EntryRef<'a, K, V, A>>, Among<K::Error, E, Error>>
  where
    K::Ref<'a>: KeyRef<'a, K>,
  {
    self.check_height_and_ro(height).map_err(Either::Right)?;

    let key: MaybeStructured<'_, K> = key.into();
    self
      .update(
        version,
        trailer,
        height.into(),
        Key::from((false, key)),
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
  /// Unlike [`get_or_insert_with_builders`](SkipList::get_or_insert_with_builders), this method will update the value if the key with the given version already exists.
  ///
  /// This method is useful when you want to insert a key and you know the key size and value size but you do not have the key and value
  /// at this moment.
  ///
  /// A placeholder will be inserted first, then you will get an [`VacantBuffer`],
  /// and you must fill the buffer with bytes later in the closure.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  pub fn insert_at_height_with_builders<'a, 'b: 'a, KE, VE>(
    &'a self,
    version: Version,
    height: Height,
    key_builder: KeyOptions<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueOptions<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
    trailer: A::Trailer,
  ) -> Result<Option<EntryRef<'a, K, V, A>>, Among<KE, VE, Error>>
  where
    K::Ref<'a>: KeyRef<'a, K>,
  {
    self.check_height_and_ro(height).map_err(Among::Right)?;

    let (key_size, key) = key_builder.into_components();
    let (offset, vk) = self
      .arena
      .fetch_vacant_key(u32::from(key_size), key)
      .map_err(Among::from_either_to_left_right)?;

    self
      .update(
        version,
        trailer,
        height.into(),
        Key::Vacant { offset, buf: vk },
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
      .map_err(|e| match e {
        Among::Left(_) => unreachable!(),
        Among::Right(e) => Among::Right(e),
        Among::Middle(e) => Among::Middle(e),
      })
  }

  /// Inserts a new key if it does not yet exist.
  ///
  /// Unlike [`insert_at_height_with_builders`](SkipList::insert_at_height_with_builders), this method will not update the value if the key with the given version already exists.
  ///
  /// This method is useful when you want to get_or_insert a key and you know the value size but you do not have the value
  /// at this moment.
  ///
  /// A placeholder will be inserted first, then you will get an [`VacantBuffer`],
  /// and you must fill the buffer with bytes later in the closure.
  pub fn get_or_insert_at_height_with_builders<'a, KE, VE>(
    &'a self,
    version: Version,
    height: Height,
    key_builder: KeyOptions<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
    value_builder: ValueOptions<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
    trailer: A::Trailer,
  ) -> Result<Option<EntryRef<'a, K, V, A>>, Among<KE, VE, Error>>
  where
    K::Ref<'a>: KeyRef<'a, K>,
  {
    if self.arena.read_only() {
      return Err(Among::Right(Error::read_only()));
    }

    let (key_size, key) = key_builder.into_components();
    let (offset, vk) = self
      .arena
      .fetch_vacant_key(u32::from(key_size), key)
      .map_err(Among::from_either_to_left_right)?;

    self
      .update(
        version,
        trailer,
        height.into(),
        Key::Vacant { offset, buf: vk },
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
      .map_err(|e| match e {
        Among::Left(_) => unreachable!(),
        Among::Right(e) => Among::Right(e),
        Among::Middle(e) => Among::Middle(e),
      })
  }

  /// Removes the key-value pair if it exists. A CAS operation will be used to ensure the operation is atomic.
  ///
  /// Unlike [`get_or_remove_at_height`](SkipList::get_or_remove_at_height), this method will remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)`:
  ///   - if the remove operation is successful or the key is marked in remove status by other threads.
  /// - Returns `Ok(Either::Right(current))` if the key with the given version already exists
  ///   and the entry is not successfully removed because of an update on this entry happens in another thread.
  #[allow(single_use_lifetimes)]
  pub fn compare_remove_at_height<'a, 'b: 'a>(
    &'a self,
    version: Version,
    height: Height,
    key: impl Into<MaybeStructured<'b, K>>,
    trailer: A::Trailer,
    success: Ordering,
    failure: Ordering,
  ) -> Result<Option<EntryRef<'a, K, V, A>>, Either<K::Error, Error>>
  where
    K::Ref<'a>: KeyRef<'a, K>,
  {
    self.check_height_and_ro(height).map_err(Either::Right)?;

    let key: MaybeStructured<'_, K> = key.into();

    self
      .update(
        version,
        trailer,
        height.into(),
        Key::from((true, key)),
        Option::<RemoveValueOptions<V::Error>>::None,
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
      .map_err(Among::into_left_right)
  }

  /// Gets or removes the key-value pair if it exists.
  /// Unlike [`compare_remove_at_height`](SkipList::compare_remove_at_height), this method will not remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key does not exist.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists.
  #[allow(single_use_lifetimes)]
  pub fn get_or_remove_at_height<'a, 'b: 'a>(
    &'a self,
    version: Version,
    height: Height,
    key: impl Into<MaybeStructured<'b, K>>,
    trailer: A::Trailer,
  ) -> Result<Option<EntryRef<'a, K, V, A>>, Either<K::Error, Error>>
  where
    K::Ref<'a>: KeyRef<'a, K>,
  {
    self.check_height_and_ro(height).map_err(Either::Right)?;
    let key: MaybeStructured<'_, K> = key.into();

    self
      .update(
        version,
        trailer,
        height.into(),
        Key::from((true, key)),
        Option::<RemoveValueOptions<V::Error>>::None,
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
      .map_err(Among::into_left_right)
  }

  /// Gets or removes the key-value pair if it exists.
  /// Unlike [`compare_remove_at_height`](SkipList::compare_remove_at_height), this method will not remove the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key does not exist.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists.
  ///
  /// This method is useful when you want to get_or_remove a key and you know the key size but you do not have the key
  /// at this moment.
  ///
  /// A placeholder will be inserted first, then you will get an [`VacantBuffer`],
  /// and you must fill the buffer with bytes later in the closure.
  pub fn get_or_remove_at_height_with_builder<'a, 'b: 'a, E>(
    &'a self,
    version: Version,
    height: Height,
    key_builder: KeyOptions<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    trailer: A::Trailer,
  ) -> Result<Option<EntryRef<'a, K, V, A>>, Either<E, Error>>
  where
    K::Ref<'a>: KeyRef<'a, K>,
  {
    self.check_height_and_ro(height).map_err(Either::Right)?;

    let (key_size, key) = key_builder.into_components();
    let (offset, vk) = self.arena.fetch_vacant_key(u32::from(key_size), key)?;
    let key = Key::RemoveVacant { offset, buf: vk };
    self
      .update(
        version,
        trailer,
        height.into(),
        key,
        Option::<RemoveValueOptions<V::Error>>::None,
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
      .map_err(|e| match e {
        Among::Right(e) => Either::Right(e),
        _ => unreachable!(),
      })
  }
}
