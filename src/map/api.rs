use super::*;

impl<T, C> SkipMap<T, C> {
  /// Returns the height of the highest tower within any of the nodes that
  /// have ever been allocated as part of this skiplist.
  #[inline]
  pub fn height(&self) -> u32 {
    self.arena.height()
  }

  /// Returns the number of remaining bytes can be allocated by the arena.
  #[inline]
  pub fn remaining(&self) -> usize {
    self.arena.remaining()
  }

  /// Returns the number of bytes that have allocated from the arena.
  #[inline]
  pub fn allocated(&self) -> usize {
    self.arena.size()
  }

  /// Returns the capacity of the arena.
  #[inline]
  pub const fn capacity(&self) -> usize {
    self.arena.capacity()
  }

  /// Returns the number of entries in the skipmap.
  #[inline]
  pub fn len(&self) -> usize {
    self.arena.len() as usize
  }

  /// Returns true if the skipmap is empty.
  #[inline]
  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }

  /// Gets the number of pointers to this `SkipMap` similar to [`Arc::strong_count`](std::sync::Arc::strong_count).
  #[inline]
  pub fn refs(&self) -> usize {
    self.arena.refs()
  }

  /// Returns how many bytes are discarded by the ARENA.
  #[inline]
  pub fn discarded(&self) -> usize {
    self.arena.discard() as usize
  }

  /// Returns the maximum version of all entries in the map.
  #[inline]
  pub fn max_version(&self) -> u64 {
    self.arena.max_version()
  }

  /// Returns the minimum version of all entries in the map.
  #[inline]
  pub fn min_version(&self) -> u64 {
    self.arena.min_version()
  }

  /// Returns the comparator used to compare keys.
  #[inline]
  pub const fn comparator(&self) -> &C {
    &self.cmp
  }

  /// Flushes outstanding memory map modifications to disk.
  ///
  /// When this method returns with a non-error result,
  /// all outstanding changes to a file-backed memory map are guaranteed to be durably stored.
  /// The file's metadata (including last modification timestamp) may not be updated.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn flush(&self) -> std::io::Result<()> {
    self.arena.flush()
  }

  /// Asynchronously flushes outstanding memory map modifications to disk.
  ///
  /// This method initiates flushing modified pages to durable storage, but it will not wait for
  /// the operation to complete before returning. The file's metadata (including last
  /// modification timestamp) may not be updated.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn flush_async(&self) -> std::io::Result<()> {
    self.arena.flush_async()
  }

  #[cfg(all(test, feature = "std"))]
  #[inline]
  pub(crate) fn with_yield_now(mut self) -> Self {
    self.yield_now = true;
    self
  }
}

impl SkipMap {
  /// Create a new skipmap according to the given capacity
  ///
  /// **Note:** The capacity stands for how many memory allocated,
  /// it does not mean the skiplist can store `cap` entries.
  ///
  ///
  ///
  /// **What the difference between this method and [`SkipMap::mmap_anon`]?**
  ///
  /// 1. This method will use an `AlignedVec` ensures we are working within Rust's memory safety guarantees.
  ///   Even if we are working with raw pointers with `Box::into_raw`,
  ///   the backend ARENA will reclaim the ownership of this memory by converting it back to a `Box`
  ///   when dropping the backend ARENA. Since `AlignedVec` uses heap memory, the data might be more cache-friendly,
  ///   especially if you're frequently accessing or modifying it.
  ///
  /// 2. Where as [`SkipMap::mmap_anon`] will use mmap anonymous to require memory from the OS.
  ///   If you require very large contiguous memory regions, `mmap` might be more suitable because
  ///   it's more direct in requesting large chunks of memory from the OS.
  ///
  /// [`SkipMap::mmap_anon`]: #method.mmap_anon
  pub fn new(cap: usize) -> Result<Self, Error> {
    Self::with_comparator(cap, Ascend)
  }

  /// Create a new skipmap according to the given capacity, and mmaped to a file.
  ///
  /// **Note:** The capacity stands for how many memory mmaped,
  /// it does not mean the skipmap can store `cap` entries.
  ///
  /// `lock`: whether to lock the underlying file or not
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn mmap_mut<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> std::io::Result<Self> {
    Self::mmap_mut_with_comparator(path, open_options, mmap_options, Ascend)
  }

  /// Open an exist file and mmap it to create skipmap.
  ///
  /// `lock`: whether to lock the underlying file or not
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn mmap<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> std::io::Result<Self> {
    Self::mmap_with_comparator(path, open_options, mmap_options, Ascend)
  }

  /// Create a new skipmap according to the given capacity, and mmap anon.
  ///
  /// **What the difference between this method and [`SkipMap::new`]?**
  ///
  /// 1. This method will use mmap anonymous to require memory from the OS directly.
  ///   If you require very large contiguous memory regions, this method might be more suitable because
  ///   it's more direct in requesting large chunks of memory from the OS.
  ///
  /// 2. Where as [`SkipMap::new`] will use an `AlignedVec` ensures we are working within Rust's memory safety guarantees.
  ///   Even if we are working with raw pointers with `Box::into_raw`,
  ///   the backend ARENA will reclaim the ownership of this memory by converting it back to a `Box`
  ///   when dropping the backend ARENA. Since `AlignedVec` uses heap memory, the data might be more cache-friendly,
  ///   especially if you're frequently accessing or modifying it.
  ///
  /// [`SkipMap::new`]: #method.new
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn mmap_anon(mmap_options: MmapOptions) -> std::io::Result<Self> {
    Self::mmap_anon_with_comparator(mmap_options, Ascend)
  }
}

impl<T, C> SkipMap<T, C> {
  /// Like [`SkipMap::new`], but with a custom comparator.
  pub fn with_comparator(cap: usize, cmp: C) -> Result<Self, Error> {
    let arena = Arena::new_vec(cap, Node::<T>::min_cap(), Node::<T>::ALIGN as usize);
    Self::new_in(arena, cmp, false)
  }

  /// Like [`SkipMap::mmap_mut`], but with a custom comparator.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn mmap_mut_with_comparator<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    cmp: C,
  ) -> std::io::Result<Self> {
    let alignment = Node::<T>::ALIGN as usize;
    let min_cap = Node::<T>::min_cap();
    let arena = Arena::mmap_mut(path, open_options, mmap_options, min_cap, alignment)?;
    Self::new_in(arena, cmp, false).map_err(invalid_data)
  }

  /// Like [`SkipMap::mmap`], but with a custom comparator.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn mmap_with_comparator<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    cmp: C,
  ) -> std::io::Result<Self> {
    let alignment = Node::<T>::ALIGN as usize;
    let min_cap = Node::<T>::min_cap();
    let arena = Arena::mmap(path, open_options, mmap_options, min_cap, alignment)?;
    Self::new_in(arena, cmp, true).map_err(invalid_data)
  }

  /// Like [`SkipMap::mmap_anon`], but with a custom comparator.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn mmap_anon_with_comparator(mmap_options: MmapOptions, cmp: C) -> std::io::Result<Self> {
    let alignment = Node::<T>::ALIGN as usize;
    let min_cap = Node::<T>::min_cap();
    let arena = Arena::new_anonymous_mmap(mmap_options, min_cap, alignment)?;
    Self::new_in(arena, cmp, false).map_err(invalid_data)
  }

  /// Clear the skiplist to empty and re-initialize.
  ///
  /// # Safety
  /// This mehod is not concurrency safe, invokers must ensure that no other threads are accessing the skipmap.
  pub unsafe fn clear(&mut self) -> Result<(), Error> {
    if self.ro {
      return Err(Error::Readonly);
    }

    let head = Node::new_empty_node_ptr(&self.arena)
      .expect("arena is not large enough to hold the head node");
    let tail = Node::new_empty_node_ptr(&self.arena)
      .expect("arena is not large enough to hold the tail node");

    // Safety:
    // We will always allocate enough space for the head node and the tail node.
    unsafe {
      // Link all head/tail levels together.
      for i in 0..MAX_HEIGHT {
        let head_link = head.tower(&self.arena, i);
        let tail_link = tail.tower(&self.arena, i);
        head_link.next_offset.store(tail.offset, Ordering::Relaxed);
        tail_link.prev_offset.store(head.offset, Ordering::Relaxed);
      }
    }

    self.head = head;
    self.tail = tail;
    self.arena.clear();
    Ok(())
  }
}

impl<T: Trailer, C: Comparator> SkipMap<T, C> {
  /// Upserts a new key-value pair if it does not yet exist, if the key with the given version already exists, it will update the value.
  /// Unlike [`insert`](SkipMap::insert), this method will update the value if the key with the given version already exists.
  ///
  /// - Returns `Ok(None)` if the key was successfully inserted.
  /// - Returns `Ok(Some(old))` if the key with the given version already exists and the value is successfully updated.
  pub fn insert<'a, 'b: 'a>(
    &'a self,
    trailer: T,
    key: &'b [u8],
    value: &'b [u8],
  ) -> Result<Option<EntryRef<'a, T, C>>, Error> {
    if self.ro {
      return Err(Error::Readonly);
    }

    let copy = |buf: &mut VacantBuffer| {
      let _ = buf.write(value);
      Ok(())
    };
    let val_len = value.len() as u32;

    self
      .update::<Infallible>(
        trailer,
        Key::Occupied(key),
        val_len,
        copy,
        Ordering::Relaxed,
        Ordering::Relaxed,
        &mut Inserter::default(),
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
  /// Unlike [`get_or_insert_with_value`](SkipMap::get_or_insert_with_value), this method will update the value if the key with the given version already exists.
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
  /// l.insert_with_value::<core::convert::Infallible>(1, b"alice", encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// })
  /// .unwrap();
  /// ```
  pub fn insert_with_value<'a, 'b: 'a, E>(
    &'a self,
    trailer: T,
    key: &'b [u8],
    value_size: u32,
    f: impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E> + Copy,
  ) -> Result<Option<EntryRef<'a, T, C>>, Either<E, Error>> {
    if self.ro {
      return Err(Either::Right(Error::Readonly));
    }

    self
      .update(
        trailer,
        Key::Occupied(key),
        value_size,
        f,
        Ordering::Relaxed,
        Ordering::Relaxed,
        &mut Inserter::default(),
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
  /// Unlike [`insert`](SkipMap::insert), this method will not update the value if the key with the given version already exists.
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

    let copy = |buf: &mut VacantBuffer| {
      let _ = buf.write(value);
      Ok(())
    };
    let val_len = value.len() as u32;

    self
      .update::<Infallible>(
        trailer,
        Key::Occupied(key),
        val_len,
        copy,
        Ordering::Relaxed,
        Ordering::Relaxed,
        &mut Inserter::default(),
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
  /// Unlike [`insert_with_value`](SkipMap::insert_with_value), this method will not update the value if the key with the given version already exists.
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
  /// l.get_or_insert_with_value::<core::convert::Infallible>(1, b"alice", encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// })
  /// .unwrap();
  /// ```
  pub fn get_or_insert_with_value<'a, 'b: 'a, E>(
    &'a self,
    trailer: T,
    key: &'b [u8],
    value_size: u32,
    f: impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E> + Copy,
  ) -> Result<Option<EntryRef<'a, T, C>>, Either<E, Error>> {
    if self.ro {
      return Err(Either::Right(Error::Readonly));
    }

    self
      .update(
        trailer,
        Key::Occupied(key),
        value_size,
        f,
        Ordering::Relaxed,
        Ordering::Relaxed,
        &mut Inserter::default(),
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
  /// Unlike [`get_or_insert_with`](SkipMap::get_or_insert_with), this method will update the value if the key with the given version already exists.
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
  /// l.insert_with::<core::convert::Infallible>(1, 5, |key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// }, encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// })
  /// .unwrap();
  /// ```
  pub fn insert_with<'a, E>(
    &'a self,
    trailer: T,
    key_size: u16,
    key: impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>,
    val_size: u32,
    val: impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E> + Copy,
  ) -> Result<Option<EntryRef<'a, T, C>>, Either<E, Error>> {
    let vk = self.fetch_vacant_key(key_size, key)?;

    self
      .update(
        trailer,
        Key::Vacant(vk),
        val_size,
        val,
        Ordering::Relaxed,
        Ordering::Relaxed,
        &mut Inserter::default(),
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
  /// Unlike [`insert_with`](SkipMap::insert_with), this method will not update the value if the key with the given version already exists.
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
  /// l.get_or_insert_with::<core::convert::Infallible>(1, 5, |key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// }, encoded_size as u32, |mut val| {
  ///   val.write(&alice.id.to_le_bytes()).unwrap();
  ///   val.write(alice.name.as_bytes()).unwrap();
  ///   Ok(())
  /// })
  /// .unwrap();
  /// ```
  pub fn get_or_insert_with<'a, E>(
    &'a self,
    trailer: T,
    key_size: u16,
    key: impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>,
    val_size: u32,
    val: impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E> + Copy,
  ) -> Result<Option<EntryRef<'a, T, C>>, Either<E, Error>> {
    let vk = self.fetch_vacant_key(key_size, key)?;

    self
      .update(
        trailer,
        Key::Vacant(vk),
        val_size,
        val,
        Ordering::Relaxed,
        Ordering::Relaxed,
        &mut Inserter::default(),
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
  /// Unlike [`get_or_remove`](SkipMap::get_or_remove), this method will remove the value if the key with the given version already exists.
  ///
  ///
  /// - Returns `Ok(Either::Left(None))`:
  ///   - if the key with the given version does not exist in the skipmap.
  ///   - if the key with the given version already exists and the entry is already removed.
  /// - Returns `Ok(Either::Left(Some(old)))` if the key with the given version already exists and the entry is successfully removed.
  /// - Returns `Ok(Either::Right(current))` if the key with the given version already exists
  /// and the entry is not successfully removed because of an update on this entry happens in another thread.
  pub fn compare_remove<'a, 'b: 'a>(
    &'a self,
    trailer: T,
    key: &'b [u8],
    success: Ordering,
    failure: Ordering,
  ) -> Result<Either<Option<EntryRef<'a, T, C>>, EntryRef<'a, T, C>>, Error> {
    self
      .update(
        trailer,
        Key::Remove(key),
        0,
        noop::<Infallible>,
        success,
        failure,
        &mut Inserter::default(),
        true,
      )
      .map(|res| match res {
        Either::Left(old) => match old {
          Some(old) => {
            if old.is_removed() {
              Either::Left(None)
            } else {
              Either::Left(Some(EntryRef(old)))
            }
          }
          None => Either::Left(None),
        },
        Either::Right(res) => match res {
          Ok(old) => {
            if old.is_removed() {
              Either::Left(None)
            } else {
              Either::Left(Some(EntryRef(old)))
            }
          }
          Err(current) => {
            if current.is_removed() {
              Either::Left(None)
            } else {
              Either::Right(EntryRef(current))
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
  pub fn get_or_remove<'a, 'b: 'a>(
    &'a self,
    trailer: T,
    key: &'b [u8],
  ) -> Result<Option<EntryRef<'a, T, C>>, Error> {
    self
      .update(
        trailer,
        Key::Remove(key),
        0,
        noop::<Infallible>,
        Ordering::Relaxed,
        Ordering::Relaxed,
        &mut Inserter::default(),
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
  /// Unlike [`compare_remove`](SkipMap::compare_remove), this method will not remove the value if the key with the given version already exists.
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
  /// l.get_or_remove_with::<core::convert::Infallible>(1, 5, |key| {
  ///   key.write(b"alice").unwrap();
  ///   Ok(())
  /// })
  /// .unwrap();
  /// ```
  pub fn get_or_remove_with<'a, 'b: 'a, E>(
    &'a self,
    trailer: T,
    key_size: u16,
    key: impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>,
  ) -> Result<Option<EntryRef<'a, T, C>>, Either<E, Error>> {
    let vk = self.fetch_vacant_key(key_size, key)?;

    self
      .update(
        trailer,
        Key::RemoveVacant(vk),
        0,
        noop::<Infallible>,
        Ordering::Relaxed,
        Ordering::Relaxed,
        &mut Inserter::default(),
        false,
      )
      .map(|res| match res {
        Either::Left(old) => match old {
          Some(old) => {
            self.arena.incr_discard(key_size as u32);

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

  /// Returns true if the key exists in the map.
  #[inline]
  pub fn contains_key<'a, 'b: 'a>(&'a self, version: u64, key: &'b [u8]) -> bool {
    self.get(version, key).is_some()
  }

  /// Returns the first entry in the map.
  pub fn first(&self, version: u64) -> Option<EntryRef<'_, T, C>> {
    self.iter(version).seek_lower_bound(Bound::Unbounded)
  }

  /// Returns the last entry in the map.
  pub fn last(&self, version: u64) -> Option<EntryRef<'_, T, C>> {
    self.iter(version).seek_upper_bound(Bound::Unbounded)
  }

  /// Returns the value associated with the given key, if it exists.
  pub fn get<'a, 'b: 'a>(&'a self, version: u64, key: &'b [u8]) -> Option<EntryRef<'a, T, C>> {
    unsafe {
      let (n, eq) = self.find_near(version, key, false, true); // findLessOrEqual.

      let n = n?;
      let node = n.as_ptr();
      let node_key = node.get_key(&self.arena);
      let (trailer, value) = node.get_value_and_trailer(&self.arena);
      if eq {
        return value.map(|val| {
          EntryRef(VersionedEntryRef {
            map: self,
            key: node_key,
            trailer,
            value: Some(val),
            ptr: n,
          })
        });
      }

      if !matches!(self.cmp.compare(key, node_key), cmp::Ordering::Equal) {
        return None;
      }

      if trailer.version() > version {
        return None;
      }

      value.map(|val| {
        EntryRef(VersionedEntryRef {
          map: self,
          key: node_key,
          trailer,
          value: Some(val),
          ptr: n,
        })
      })
    }
  }

  /// Returns an `EntryRef` pointing to the highest element whose key is below the given bound.
  /// If no such element is found then `None` is returned.
  pub fn upper_bound<'a, 'b: 'a>(
    &'a self,
    version: u64,
    upper: Bound<&'b [u8]>,
  ) -> Option<EntryRef<'a, T, C>> {
    self.iter(version).seek_upper_bound(upper)
  }

  /// Returns an `EntryRef` pointing to the lowest element whose key is above the given bound.
  /// If no such element is found then `None` is returned.
  pub fn lower_bound<'a, 'b: 'a>(
    &'a self,
    version: u64,
    lower: Bound<&'b [u8]>,
  ) -> Option<EntryRef<'a, T, C>> {
    self.iter(version).seek_lower_bound(lower)
  }

  /// Returns a new iterator, this iterator will yield the latest version of all entries in the map less or equal to the given version.
  #[inline]
  pub const fn iter(&self, version: u64) -> iterator::Iter<T, C> {
    iterator::Iter::new(version, self)
  }

  /// Returns a new iterator, this iterator will yield all versions for all entries in the map less or equal to the given version.
  #[inline]
  pub const fn iter_all_versions(&self, version: u64) -> iterator::AllVersionsIter<T, C> {
    iterator::AllVersionsIter::new(version, self, true)
  }

  /// Returns a iterator that within the range, this iterator will yield the latest version of all entries in the range less or equal to the given version.
  #[inline]
  pub fn range<'a, Q, R>(&'a self, version: u64, range: R) -> iterator::Iter<'a, T, C, Q, R>
  where
    &'a [u8]: PartialOrd<Q>,
    Q: ?Sized + PartialOrd<&'a [u8]>,
    R: RangeBounds<Q> + 'a,
  {
    iterator::Iter::range(version, self, range)
  }

  /// Returns a iterator that within the range, this iterator will yield all versions for all entries in the range less or equal to the given version.
  #[inline]
  pub fn range_all_versions<'a, Q, R>(
    &'a self,
    version: u64,
    range: R,
  ) -> iterator::AllVersionsIter<'a, T, C, Q, R>
  where
    &'a [u8]: PartialOrd<Q>,
    Q: ?Sized + PartialOrd<&'a [u8]>,
    R: RangeBounds<Q> + 'a,
  {
    iterator::AllVersionsIter::range(version, self, range, true)
  }
}
