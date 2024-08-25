use base::Error;
use either::Either;

use super::*;
use core::mem;

pub(crate) struct Deallocator {
  node: Option<Pointer>,
  key: Option<Pointer>,
  value: Option<Pointer>,
}

impl Deallocator {
  #[inline]
  fn dealloc<A: Allocator>(self, arena: &A) {
    if let Some(ptr) = self.node {
      arena.dealloc(ptr.offset, ptr.size);
    }

    if let Some(ptr) = self.key {
      arena.dealloc(ptr.offset, ptr.size);
    }

    if let Some(ptr) = self.value {
      arena.dealloc(ptr.offset, ptr.size);
    }
  }

  #[inline]
  fn dealloc_node_and_key<A: Allocator>(self, arena: &A) {
    if let Some(ptr) = self.node {
      arena.dealloc(ptr.offset, ptr.size);
    }

    if let Some(ptr) = self.key {
      arena.dealloc(ptr.offset, ptr.size);
    }
  }

  #[inline]
  fn dealloc_key_by_ref<A: Allocator>(&mut self, arena: &A) {
    if let Some(ptr) = self.key.take() {
      arena.dealloc(ptr.offset, ptr.size);
    }
  }
}

pub(crate) trait ValuePointer {
  /// The tombstone value.
  const REMOVE: u32;

  fn swap(&self, offset: u32, size: u32) -> (u32, u32);
}

pub(crate) trait Node: Sized {
  type Link;
  type Trailer;
  type ValuePointer: ValuePointer;

  fn full(value_offset: u32, max_height: u8) -> Self;

  fn size(max_height: u8) -> usize {
    mem::size_of::<Self>() + (max_height as usize) * mem::size_of::<Self::Link>()
  }

  fn value(&self) -> &Self::ValuePointer;

  fn set_value(&mut self, offset: u32, size: u32);

  fn set_key_size_and_height(&mut self, key_size_and_height: u32);

  fn set_key_offset(&mut self, key_offset: u32);

  fn set_version(&mut self, version: Version);
}

pub(crate) trait NodePtr {
  type Node: Node;

  const NULL: Self;

  fn new(ptr: *mut u8, offset: u32) -> Self;
}

pub(crate) trait BytesRefMut {
  fn offset(&self) -> u32;

  fn capacity(&self) -> u32;

  fn memory_offset(&self) -> usize;

  fn memory_capacity(&self) -> usize;

  fn detach(&mut self);

  fn as_mut_ptr(&self) -> *mut u8;
}

pub(crate) trait RefMut<T> {
  fn offset(&self) -> u32;

  fn memory_offset(&self) -> usize;

  fn memory_capacity(&self) -> usize;

  fn detach(&mut self);

  fn as_mut_ptr(&self) -> *mut u8;

  fn write(&mut self, value: T);
}

pub(crate) unsafe trait Allocator: Sized {
  type Node: Node;
  type NodePtr: NodePtr<Node = Self::Node>;
  type BytesRefMut<'a>: BytesRefMut
  where
    Self: 'a;
  type RefMut<'a, T>: RefMut<T>
  where
    Self: 'a;

  /// Allocates a byte slice that can hold a well-aligned `T` and extra `size` bytes.
  ///
  /// The layout of the allocated memory is:
  ///
  /// ```text
  /// | T | [u8; size] |
  /// ```
  fn alloc_aligned_bytes<T>(&self, size: u32) -> Result<Self::BytesRefMut<'_>, ArenaError>;

  /// Allocates a slice of memory in the ARENA.
  fn alloc_bytes(&self, size: u32) -> Result<Self::BytesRefMut<'_>, ArenaError>;

  /// Allocates a `T` in the Allocator.
  fn alloc<T>(&self) -> Result<Self::RefMut<'_, T>, ArenaError>;

  /// Returns a mutable bytes slice from the ARENA.
  /// If the ARENA is read-only, then this method will return an empty slice.
  ///
  /// # Safety
  /// - `offset..offset + size` must be allocated memory.
  /// - `offset` must be less than the capacity of the ARENA.
  /// - `size` must be less than the capacity of the ARENA.
  /// - `offset + size` must be less than the capacity of the ARENA.
  ///
  /// # Panic
  /// - If the ARENA is read-only, then this method will panic.
  #[allow(clippy::mut_from_ref)]
  fn get_bytes_mut(&self, offset: usize, size: usize) -> &mut [u8];

  /// Deallocates the memory at the given offset and size, the `offset..offset + size` will be made to a segment,
  /// returns `true` if the deallocation is successful.
  ///
  /// # Safety
  /// - you must ensure the same `offset..offset + size` is not deallocated twice.
  /// - `offset` must be larger than the [`Self::data_offset`].
  /// - `offset + size` must be less than the [`Self::allocated`].
  fn dealloc(&self, offset: u32, size: u32) -> bool;

  #[inline]
  fn fill_vacant_key<'a, E>(
    &'a self,
    size: u32,
    offset: u32,
    f: impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>,
  ) -> Result<(u32, Pointer), E> {
    let buf = self.get_bytes_mut(offset as usize, size as usize);
    let mut oval = VacantBuffer::new(size as usize, offset, buf);
    if let Err(e) = f(&mut oval) {
      self.dealloc(offset, size);
      return Err(e);
    }

    let len = oval.len();
    let remaining = oval.remaining();
    if remaining != 0 {
      #[cfg(feature = "tracing")]
      tracing::warn!("vacant value is not fully filled, remaining {remaining} bytes");
      let deallocated = self.dealloc(offset + len as u32, remaining as u32);
      if deallocated {
        return Ok((
          oval.len() as u32,
          Pointer::new(offset, size - remaining as u32),
        ));
      }
    }
    Ok((oval.len() as u32, Pointer::new(offset, size)))
  }

  #[inline]
  fn fill_vacant_value<'a, E>(
    &'a self,
    offset: u32,
    size: u32,
    value_size: u32,
    value_offset: u32,
    f: impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>,
  ) -> Result<(u32, Pointer), E> {
    let buf = self.get_bytes_mut(value_offset as usize, value_size as usize);
    let mut oval = VacantBuffer::new(value_size as usize, value_offset, buf);
    if let Err(e) = f(&mut oval) {
      self.dealloc(offset, size);
      return Err(e);
    }

    let len = oval.len();
    let remaining = oval.remaining();
    if remaining != 0 {
      #[cfg(feature = "tracing")]
      tracing::warn!("vacant value is not fully filled, remaining {remaining} bytes");
      let deallocated = self.dealloc(value_offset + len as u32, remaining as u32);

      if deallocated {
        return Ok((
          oval.len() as u32,
          Pointer::new(offset, size - remaining as u32),
        ));
      }
    }

    Ok((oval.len() as u32, Pointer::new(offset, size)))
  }

  #[inline]
  fn allocate_pure_node(&self, height: u32) -> Result<Self::BytesRefMut<'_>, ArenaError> {
    self.alloc_aligned_bytes::<Self::Node>(
      height * mem::size_of::<<Self::Node as Node>::Link>() as u32,
    )
  }

  /// Allocates a `Node`, key, trailer and value
  fn allocate_entry_node<'a, 'b: 'a, E>(
    &'a self,
    version: Version,
    height: u32,
    trailer: <Self::Node as Node>::Trailer,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<(Self::NodePtr, Deallocator), Either<E, Error>> {
    let (key_size, kf) = key_builder.into_components();
    let (value_size, vf) = value_builder.into_components();

    self
      .check_node_size(height, key_size.to_u32(), value_size)
      .map_err(Either::Right)?;

    unsafe {
      let mut node = self
        .allocate_pure_node(height)
        .map_err(|e| Either::Right(e.into()))?;
      let node_ptr = node.as_mut_ptr().cast::<Self::Node>();
      let node_offset = node.offset();

      let mut key = self
        .alloc_bytes(key_size.to_u32())
        .map_err(|e| Either::Right(e.into()))?;
      let key_offset = key.offset();
      let key_cap = key.capacity();
      let mut trailer_and_value = self
        .alloc_aligned_bytes::<<Self::Node as Node>::Trailer>(value_size)
        .map_err(|e| Either::Right(e.into()))?;
      let trailer_offset = trailer_and_value.offset();
      let trailer_ptr = trailer_and_value
        .as_mut_ptr()
        .cast::<<Self::Node as Node>::Trailer>();
      trailer_ptr.write(trailer);

      let value_offset = trailer_offset + mem::size_of::<<Self::Node as Node>::Trailer>() as u32;

      // Safety: the node is well aligned
      let node_ref = &mut *node_ptr;
      node_ref.set_value(trailer_offset, value_size);
      node_ref.set_key_offset(key_offset);
      node_ref.set_key_size_and_height(encode_key_size_and_height(key_cap as u32, height as u8));
      node_ref.set_version(version);

      key.detach();
      let (_, key_deallocate_info) = self
        .fill_vacant_key(key_cap as u32, key_offset as u32, kf)
        .map_err(Either::Left)?;
      trailer_and_value.detach();
      let (_, value_deallocate_info) = self
        .fill_vacant_value(
          trailer_offset as u32,
          trailer_and_value.capacity() as u32,
          value_size,
          value_offset,
          vf,
        )
        .map_err(Either::Left)?;
      node.detach();

      let deallocator = Deallocator {
        node: Some(Pointer::new(node_offset as u32, node.capacity() as u32)),
        key: Some(key_deallocate_info),
        value: Some(value_deallocate_info),
      };

      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      if let Err(e) = self.flush_node(
        (node_offset as u32, node.capacity() as u32),
        Some((key_offset as u32, key.capacity() as u32)),
        Some((
          trailer_and_value.memory_offset() as u32,
          trailer_and_value.memory_capacity() as u32,
        )),
      ) {
        deallocator.dealloc(self);

        return Err(Either::Right(e));
      }

      Ok((NodePtr::new(node_ptr as _, node_offset as u32), deallocator))
    }
  }

  /// Allocates a `Node` and trailer
  fn allocate_node_in<'a, 'b: 'a, E>(
    &'a self,
    version: Version,
    height: u32,
    trailer: <Self::Node as Node>::Trailer,
    key_offset: u32,
    key_size: u32,
    value_size: u32,
  ) -> Result<(Self::NodePtr, Deallocator), Either<E, Error>> {
    self
      .check_node_size(height, key_size, value_size)
      .map_err(Either::Right)?;

    unsafe {
      let mut node = self
        .alloc_aligned_bytes::<Self::Node>(
          height * mem::size_of::<<Self::Node as Node>::Link>() as u32,
        )
        .map_err(|e| Either::Right(e.into()))?;
      let node_ptr = node.as_mut_ptr().cast::<Self::Node>();
      let node_offset = node.offset();

      let mut trailer_ref = self
        .alloc::<<Self::Node as Node>::Trailer>()
        .map_err(|e| Either::Right(e.into()))?;
      let trailer_offset = trailer_ref.offset();
      trailer_ref.write(trailer);

      // Safety: the node is well aligned
      let node_ref = &mut *node_ptr;
      node_ref.set_value(trailer_offset, value_size);
      node_ref.set_key_offset(key_offset);
      node_ref.set_key_size_and_height(encode_key_size_and_height(key_size, height as u8));
      node_ref.set_version(version);

      trailer_ref.detach();
      node.detach();

      let deallocator = Deallocator {
        node: Some(Pointer::new(node_offset as u32, node.capacity() as u32)),
        key: None,
        value: Some(Pointer::new(
          trailer_offset as u32,
          mem::size_of::<<Self::Node as Node>::Trailer>() as u32,
        )),
      };

      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      if let Err(e) = self.flush_node(
        (node_offset as u32, node.capacity() as u32),
        None,
        Some((
          trailer_ref.memory_offset() as u32,
          trailer_ref.memory_capacity() as u32,
        )),
      ) {
        deallocator.dealloc(self);
        return Err(Either::Right(e));
      }

      Ok((NodePtr::new(node_ptr as _, node_offset as u32), deallocator))
    }
  }

  /// Allocates a `Node`, key and trailer
  fn allocate_key_node<'a, 'b: 'a, E>(
    &'a self,
    version: Version,
    height: u32,
    trailer: <Self::Node as Node>::Trailer,
    key_size: u32,
    kf: impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>,
    value_size: u32,
  ) -> Result<(Self::NodePtr, Deallocator), Either<E, Error>> {
    self
      .check_node_size(height, key_size, value_size)
      .map_err(Either::Right)?;

    unsafe {
      let mut node = self
        .alloc_aligned_bytes::<Self::Node>(
          height * mem::size_of::<<Self::Node as Node>::Link>() as u32,
        )
        .map_err(|e| Either::Right(e.into()))?;
      let node_ptr = node.as_mut_ptr().cast::<Self::Node>();
      let node_offset = node.offset();

      let mut key = self
        .alloc_bytes(key_size)
        .map_err(|e| Either::Right(e.into()))?;
      let key_offset = key.offset();
      let key_cap = key.capacity();

      let mut trailer_ref = self
        .alloc::<<Self::Node as Node>::Trailer>()
        .map_err(|e| Either::Right(e.into()))?;
      let trailer_offset = trailer_ref.offset();
      trailer_ref.write(trailer);

      // Safety: the node is well aligned
      let node_ref = &mut *node_ptr;
      node_ref.set_value(trailer_offset, value_size);
      node_ref.set_key_offset(key_offset);
      node_ref.set_key_size_and_height(encode_key_size_and_height(key_cap as u32, height as u8));
      node_ref.set_version(version);

      key.detach();
      let (_, key_deallocate_info) = self
        .fill_vacant_key(key_cap as u32, key_offset as u32, kf)
        .map_err(Either::Left)?;

      trailer_ref.detach();
      node.detach();

      let deallocator = Deallocator {
        node: Some(Pointer::new(node_offset as u32, node.capacity() as u32)),
        key: Some(key_deallocate_info),
        value: Some(Pointer::new(
          trailer_offset as u32,
          mem::size_of::<<Self::Node as Node>::Trailer>() as u32,
        )),
      };

      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      if let Err(e) = self.flush_node(
        (node_offset as u32, node.capacity() as u32),
        Some((key_offset as u32, key.capacity() as u32)),
        Some((
          trailer_ref.memory_offset() as u32,
          trailer_ref.memory_capacity() as u32,
        )),
      ) {
        deallocator.dealloc(self);
        return Err(Either::Right(e));
      }

      Ok((NodePtr::new(node_ptr as _, node_offset as u32), deallocator))
    }
  }

  /// Allocates a `Node`, trailer and value
  fn allocate_value_node<'a, 'b: 'a, E>(
    &'a self,
    version: Version,
    height: u32,
    trailer: <Self::Node as Node>::Trailer,
    key_size: u32,
    key_offset: u32,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<(Self::NodePtr, Deallocator), Either<E, Error>> {
    let (value_size, vf) = value_builder.into_components();
    self
      .check_node_size(height, key_size, value_size)
      .map_err(Either::Right)?;

    unsafe {
      let mut node = self
        .alloc_aligned_bytes::<Self::Node>(
          height * mem::size_of::<<Self::Node as Node>::Link>() as u32,
        )
        .map_err(|e| Either::Right(e.into()))?;
      let node_ptr = node.as_mut_ptr().cast::<Self::Node>();
      let node_offset = node.offset();

      let mut trailer_and_value = self
        .alloc_aligned_bytes::<<Self::Node as Node>::Trailer>(value_size)
        .map_err(|e| Either::Right(e.into()))?;
      let trailer_offset = trailer_and_value.offset();
      let trailer_ptr = trailer_and_value
        .as_mut_ptr()
        .cast::<<Self::Node as Node>::Trailer>();
      trailer_ptr.write(trailer);
      let value_offset = trailer_offset + mem::size_of::<<Self::Node as Node>::Trailer>() as u32;

      // Safety: the node is well aligned
      let node_ref = &mut *node_ptr;
      node_ref.set_value(trailer_offset, value_size);
      node_ref.set_key_offset(key_offset);
      node_ref.set_key_size_and_height(encode_key_size_and_height(key_size, height as u8));
      node_ref.set_version(version);

      trailer_and_value.detach();
      let (_, value_deallocate_info) = self
        .fill_vacant_value(
          trailer_offset as u32,
          trailer_and_value.capacity() as u32,
          value_size,
          value_offset,
          vf,
        )
        .map_err(Either::Left)?;

      node.detach();

      let deallocator = Deallocator {
        node: Some(Pointer::new(node_offset as u32, node.capacity() as u32)),
        key: None,
        value: Some(value_deallocate_info),
      };

      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      if let Err(e) = self.flush_node(
        (node_offset as u32, node.capacity() as u32),
        None,
        Some((
          trailer_and_value.memory_offset() as u32,
          trailer_and_value.memory_capacity() as u32,
        )),
      ) {
        deallocator.dealloc(self);
        return Err(Either::Right(e));
      }

      Ok((NodePtr::new(node_ptr as _, node_offset as u32), deallocator))
    }
  }

  fn allocate_full_node(arena: &Arena, max_height: u8) -> Result<Self::NodePtr, ArenaError> {
    // Safety: node, links and trailer do not need to be dropped, and they are recoverable.
    unsafe {
      let mut node = arena.alloc_aligned_bytes::<Self::Node>(
        ((max_height as usize) * mem::size_of::<<Self::Node as Node>::Link>()) as u32,
      )?;

      // Safety: node and trailer do not need to be dropped.
      node.detach();

      let node_ptr = node.as_mut_ptr().cast::<Self::Node>();
      let node_offset = node.offset();

      let trailer_offset = if mem::size_of::<<Self::Node as Node>::Trailer>() != 0 {
        let mut trailer = arena.alloc::<<Self::Node as Node>::Trailer>()?;
        trailer.detach();
        trailer.offset()
      } else {
        arena.allocated()
      };

      let node = &mut *node_ptr;
      *node = <Self::Node as Node>::full(trailer_offset as u32, max_height);

      Ok(NodePtr::new(node_ptr as _, node_offset as u32))
    }
  }

  #[inline]
  fn allocate_and_set_value<'a, E>(
    &self,
    arena: &'a Arena,
    node: &Self::Node,
    trailer: <Self::Node as Node>::Trailer,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<(), Either<E, Error>> {
    let (value_size, f) = value_builder.into_components();
    let mut bytes = arena
      .alloc_aligned_bytes::<<Self::Node as Node>::Trailer>(value_size)
      .map_err(|e| Either::Right(e.into()))?;
    let trailer_ptr = bytes.as_mut_ptr().cast::<<Self::Node as Node>::Trailer>();
    let trailer_offset = bytes.offset();
    let value_offset = trailer_offset + mem::size_of::<<Self::Node as Node>::Trailer>();

    let mut oval = VacantBuffer::new(value_size as usize, value_offset as u32, unsafe {
      arena.get_bytes_mut(value_offset, value_size as usize)
    });
    f(&mut oval).map_err(Either::Left)?;

    let remaining = oval.remaining();
    let mut discard = 0;
    if remaining != 0
      && unsafe { !arena.dealloc((value_offset + oval.len()) as u32, remaining as u32) }
    {
      discard += remaining;
    }

    bytes.detach();
    unsafe {
      trailer_ptr.write(trailer);
    }

    if discard != 0 {
      arena.increase_discarded(discard as u32);
    }

    let (_, old_len) = node.value().swap(trailer_offset as u32, value_size);
    if old_len != <<Self::Node as Node>::ValuePointer as ValuePointer>::REMOVE {
      arena.increase_discarded(old_len);
    }

    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    {
      if arena.is_on_disk_and_mmap() {
        bytes.flush().map_err(|e| Either::Right(e.into()))?;
      }
    }

    Ok(())
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn is_on_disk_and_mmap(&self) -> bool;

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn flush_range(&self, offset: usize, size: usize) -> Result<(), Error>;

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn page_size(&self) -> usize;

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  fn flush_node(
    &self,
    // (offset, size)
    (node_offset, node_size): (u32, u32),
    // (offset, size)
    key: Option<(u32, u32)>,
    // (offset, size)
    value: Option<(u32, u32)>,
  ) -> Result<(), Error> {
    use arrayvec::ArrayVec;

    if self.is_on_disk_and_mmap() {
      fn calculate_page_bounds(offset: u32, size: u32, page_size: u32) -> (u32, u32) {
        let start_page = offset / page_size;
        let end_page = (offset + size).saturating_sub(1) / page_size;
        (start_page, end_page)
      }

      let page_size = self.page_size() as u32;
      let mut ranges = ArrayVec::<(u32, u32), 3>::new_const();
      ranges.push(calculate_page_bounds(node_offset, node_size, page_size));

      if let Some((offset, size)) = key {
        ranges.push(calculate_page_bounds(offset, size, page_size));
      }

      if let Some((offset, size)) = value {
        ranges.push(calculate_page_bounds(offset, size, page_size));
      }

      let len = ranges.len();

      match len {
        1 => {
          return self
            .flush_range(node_offset as usize, node_size as usize)
            .map_err(Into::into);
        }
        2..=3 => {
          // Sort ranges by start page
          ranges.sort_by_key(|&(start, _)| start);

          let mut merged_ranges = ArrayVec::<(u32, u32), 3>::new_const();

          for (start, end) in ranges {
            match merged_ranges.last_mut() {
              None => {
                merged_ranges.push((start, end));
              }
              // no overlap
              Some((_, last_end)) if *last_end < start => {
                merged_ranges.push((start, end));
              }
              // overlap
              Some((_, last)) => {
                *last = (*last).max(end);
              }
            }
          }

          for (start, end) in merged_ranges {
            let spo = (start * page_size) as usize;
            let epo = (end * page_size) as usize;
            self.flush_range(spo, (epo - spo).max(1))?;
          }

          return Ok(());
        }
        _ => unreachable!(),
      }
    }

    Ok(())
  }

  fn max_key_size(&self) -> u32;

  fn max_value_size(&self) -> u32;

  fn max_height(&self) -> u32;

  #[inline]
  fn check_node_size(&self, height: u32, key_size: u32, mut value_size: u32) -> Result<(), Error> {
    if height < 1 || height > self.max_height() {
      panic!("height cannot be less than one or greater than the max height");
    }

    if key_size > self.max_key_size() {
      return Err(Error::KeyTooLarge(key_size as u64));
    }

    // if value_size is u32::MAX, it means that the value is removed.
    value_size = if value_size == u32::MAX {
      0
    } else {
      value_size
    };

    if value_size > self.max_value_size() {
      return Err(Error::ValueTooLarge(value_size as u64));
    }

    let entry_size =
      (value_size as u64 + key_size as u64) + <Self::Node as Node>::size(height as u8) as u64;
    if entry_size > u32::MAX as u64 {
      return Err(Error::EntryTooLarge(entry_size));
    }

    Ok(())
  }
}
