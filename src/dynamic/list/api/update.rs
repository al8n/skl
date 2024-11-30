use super::{
  super::{Inserter, Key, RefCounter},
  Allocator, EntryRef, Error, Height, RemoveValueBuilder, SkipList, ValueBuilder, Version,
};
use crate::KeyBuilder;
use among::Among;
use core::sync::atomic::Ordering;
use dbutils::{buffer::VacantBuffer, equivalentor::DynComparator};
use either::Either;

impl<A, R, C> SkipList<A, R, C>
where
  A: Allocator,
  C: DynComparator<[u8], [u8]>,
  R: RefCounter,
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
    key: &'b [u8],
    value: &'b [u8],
  ) -> Result<Option<EntryRef<'a, &'a [u8], C, A, R>>, Error> {
    self.insert_at_height(version, self.random_height(), key, value)
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
    key: &'b [u8],
    value: &'b [u8],
  ) -> Result<Option<EntryRef<'a, &'a [u8], C, A, R>>, Error> {
    self.validate(height, key.len(), value.len())?;

    let val_len = value.len();
    let copy = |buf: &mut VacantBuffer<'_>| {
      buf.put_slice(value)?;
      Result::<_, dbutils::error::InsufficientBuffer>::Ok(val_len)
    };

    self
      .update(
        version,
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
            Some(old.map())
          }
        })
      })
      .map_err(Either::unwrap_right)
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
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, E>>,
  ) -> Result<Option<EntryRef<'a, &'a [u8], C, A, R>>, Either<E, Error>> {
    self
      .validate(height, key.len(), value_builder.size())
      .map_err(Either::Right)?;

    self
      .update(
        version,
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
            Some(old.map())
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
    key: &'b [u8],
    value: &'b [u8],
  ) -> Result<Option<EntryRef<'a, &'a [u8], C, A, R>>, Error> {
    self.validate(height, key.len(), value.len())?;

    let val_len = value.len();
    let copy = |buf: &mut VacantBuffer<'_>| {
      buf.put_slice(value)?;
      Result::<_, dbutils::error::InsufficientBuffer>::Ok(val_len)
    };

    self
      .update(
        version,
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
            Some(old.map())
          }
        })
      })
      .map_err(Either::unwrap_right)
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
    key: &'b [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, E>>,
  ) -> Result<Option<EntryRef<'a, &'a [u8], C, A, R>>, Either<E, Error>> {
    self
      .validate(height, key.len(), value_builder.size())
      .map_err(Either::Right)?;

    self
      .update(
        version,
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
            Some(old.map())
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
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, VE>>,
  ) -> Result<Option<EntryRef<'a, &'a [u8], C, A, R>>, Among<KE, VE, Error>> {
    self
      .validate(height, key_builder.size(), value_builder.size())
      .map_err(Among::Right)?;

    let (key_size, key) = key_builder.into_components();
    let (offset, vk) = self
      .arena
      .fetch_vacant_key(key_size as u32, key)
      .map_err(Among::from_either_to_left_right)?;

    self
      .update(
        version,
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
            Some(old.map())
          }
        })
      })
      .map_err(Among::from_either_to_middle_right)
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
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, VE>>,
  ) -> Result<Option<EntryRef<'a, &'a [u8], C, A, R>>, Among<KE, VE, Error>> {
    self
      .validate(height, key_builder.size(), value_builder.size())
      .map_err(Among::Right)?;

    let (key_size, key) = key_builder.into_components();
    let (offset, vk) = self
      .arena
      .fetch_vacant_key(key_size as u32, key)
      .map_err(Among::from_either_to_left_right)?;

    self
      .update(
        version,
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
            Some(old.map())
          }
        })
      })
      .map_err(Among::from_either_to_middle_right)
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
    key: &'b [u8],
    success: Ordering,
    failure: Ordering,
  ) -> Result<Option<EntryRef<'a, &'a [u8], C, A, R>>, Error> {
    self.validate(height, key.len(), 0)?;

    self
      .update(
        version,
        height.into(),
        Key::Remove(key),
        Option::<RemoveValueBuilder<()>>::None,
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
              Some(old.map())
            }
          }
          Err(current) => {
            if current.is_removed() {
              None
            } else {
              Some(current.map())
            }
          }
        },
      })
      .map_err(Either::unwrap_right)
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
    key: &'b [u8],
  ) -> Result<Option<EntryRef<'a, &'a [u8], C, A, R>>, Error> {
    self.validate(height, key.len(), 0)?;

    self
      .update(
        version,
        height.into(),
        Key::Remove(key),
        Option::<RemoveValueBuilder<()>>::None,
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
              Some(old.map())
            }
          }
          None => None,
        },
        _ => unreachable!("get_or_remove does not use CAS, so it must return `Either::Left`"),
      })
      .map_err(Either::unwrap_right)
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
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, E>>,
  ) -> Result<Option<EntryRef<'a, &'a [u8], C, A, R>>, Either<E, Error>> {
    self
      .validate(height, key_builder.size(), 0)
      .map_err(Either::Right)?;

    let (key_size, key) = key_builder.into_components();
    let (offset, vk) = self.arena.fetch_vacant_key(key_size as u32, key)?;
    let key = Key::RemoveVacant { offset, buf: vk };
    self
      .update(
        version,
        height.into(),
        key,
        Option::<RemoveValueBuilder<()>>::None,
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
              Some(old.map())
            }
          }
          None => None,
        },
        _ => unreachable!("get_or_remove does not use CAS, so it must return `Either::Left`"),
      })
      .map_err(|e| match e {
        Either::Right(e) => Either::Right(e),
        _ => unreachable!(),
      })
  }
}
