use either::Either;

use super::*;
use core::{mem, ptr::NonNull, sync::atomic::Ordering};

pub(crate) struct Deallocator {
  pub(crate) node: Option<Pointer>,
  pub(crate) key: Option<Pointer>,
  pub(crate) value: Option<Pointer>,
}

impl Deallocator {
  #[inline]
  pub fn dealloc<A: Allocator>(self, arena: &A) {
    unsafe {
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
  }

  #[inline]
  pub fn dealloc_node_and_key<A: Allocator>(self, arena: &A) {
    unsafe {
      if let Some(ptr) = self.node {
        arena.dealloc(ptr.offset, ptr.size);
      }

      if let Some(ptr) = self.key {
        arena.dealloc(ptr.offset, ptr.size);
      }
    }
  }

  #[inline]
  pub fn dealloc_key_by_ref<A: Allocator>(&mut self, arena: &A) {
    if let Some(ptr) = self.key.take() {
      unsafe {
        arena.dealloc(ptr.offset, ptr.size);
      }
    }
  }
}

#[derive(Debug)]
pub(crate) struct ValuePartPointer<T> {
  pub(crate) trailer_offset: u32,
  pub(crate) value_offset: u32,
  pub(crate) value_len: u32,
  _m: core::marker::PhantomData<T>,
}

impl<T> Clone for ValuePartPointer<T> {
  fn clone(&self) -> Self {
    *self
  }
}

impl<T> Copy for ValuePartPointer<T> {}

impl<T> ValuePartPointer<T> {
  #[inline]
  pub(crate) const fn new(trailer_offset: u32, value_offset: u32, value_len: u32) -> Self {
    Self {
      trailer_offset,
      value_offset,
      value_len,
      _m: core::marker::PhantomData,
    }
  }
}

pub(crate) trait ValuePointer {
  /// The tombstone value.
  const REMOVE: u32;

  fn swap(&self, offset: u32, size: u32) -> (u32, u32);

  fn load(&self) -> (u32, u32);
}

pub(crate) trait Link {
  fn new(next_offset: u32, prev_offset: u32) -> Self;

  fn store_next_offset(&self, offset: u32, ordering: Ordering);

  fn store_prev_offset(&self, offset: u32, ordering: Ordering);
}

pub(crate) trait Node: Sized + core::fmt::Debug {
  type Link: Link;
  type Trailer: Trailer;
  type ValuePointer: ValuePointer;
  type Pointer: NodePointer<Node = Self>;

  fn full(value_offset: u32, max_height: u8) -> Self;

  fn size(max_height: u8) -> usize {
    mem::size_of::<Self>() + (max_height as usize) * mem::size_of::<Self::Link>()
  }

  fn value_pointer(&self) -> &Self::ValuePointer;

  fn set_value_pointer(&mut self, offset: u32, size: u32);

  #[inline]
  fn update_value<A: Allocator>(&self, arena: &A, offset: u32, value_size: u32) {
    let (_, old_len) = self.value_pointer().swap(offset, value_size);
    if old_len != Self::ValuePointer::REMOVE {
      arena.increase_discarded(old_len);
    }
  }

  fn clear_value<A: Allocator>(
    &self,
    arena: &A,
    success: Ordering,
    failure: Ordering,
  ) -> Result<(), (u32, u32)>;

  fn set_key_size_and_height(&mut self, key_size_and_height: u32);

  fn set_key_offset(&mut self, key_offset: u32);

  fn version(&self) -> Version;

  fn set_version(&mut self, version: Version);

  fn key_size_and_height(&self) -> u32;

  fn key_offset(&self) -> u32;

  #[inline]
  fn key_size(&self) -> u32 {
    decode_key_size_and_height(self.key_size_and_height()).0
  }

  #[inline]
  fn height(&self) -> u8 {
    decode_key_size_and_height(self.key_size_and_height()).1
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  unsafe fn get_key<'a, 'b: 'a, A: Allocator>(&'a self, arena: &'b A) -> &'b [u8] {
    arena.get_bytes(self.key_offset() as usize, self.key_size() as usize)
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[inline]
  unsafe fn get_value<'a, 'b: 'a, A: Allocator>(&'a self, arena: &'b A) -> Option<&'b [u8]> {
    let (offset, len) = self.value_pointer().load();

    if len == u32::MAX {
      return None;
    }
    let align_offset = Self::align_offset(offset);
    Some(arena.get_bytes(
      align_offset as usize + mem::size_of::<Self::Trailer>(),
      len as usize,
    ))
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[inline]
  unsafe fn get_value_by_value_offset<'a, 'b: 'a, A: Allocator>(
    &'a self,
    arena: &'b A,
    offset: u32,
    len: u32,
  ) -> Option<&'b [u8]> {
    if len == u32::MAX {
      return None;
    }

    Some(arena.get_bytes(offset as usize, len as usize))
  }

  #[inline]
  fn trailer_offset_and_value_size(&self) -> ValuePartPointer<Self::Trailer> {
    let (offset, len) = self.value_pointer().load();
    let align_offset = Self::align_offset(offset);
    ValuePartPointer::new(
      align_offset,
      align_offset + mem::size_of::<Self::Trailer>() as u32,
      len,
    )
  }

  #[inline]
  unsafe fn get_trailer<'a, 'b: 'a, A: Allocator>(&'a self, arena: &'b A) -> &'b Self::Trailer {
    let (offset, _) = self.value_pointer().load();
    &*arena.get_aligned_pointer(offset as usize)
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[inline]
  unsafe fn get_trailer_by_offset<'a, 'b: 'a, A: Allocator>(
    &'a self,
    arena: &'b A,
    offset: u32,
  ) -> &'b Self::Trailer {
    &*arena.get_aligned_pointer::<Self::Trailer>(offset as usize)
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[inline]
  unsafe fn get_value_and_trailer_with_pointer<'a, 'b: 'a, A: Allocator>(
    &'a self,
    arena: &'b A,
  ) -> (
    &'b Self::Trailer,
    Option<&'b [u8]>,
    ValuePartPointer<Self::Trailer>,
  ) {
    let (offset, len) = self.value_pointer().load();
    let ptr = arena.get_aligned_pointer(offset as usize);

    let align_offset = Arena::align_offset::<Self::Trailer>(offset);
    let trailer = &*ptr;

    if len == u32::MAX {
      return (
        trailer,
        None,
        ValuePartPointer::new(
          offset,
          align_offset + mem::size_of::<Self::Trailer>() as u32,
          len,
        ),
      );
    }

    let value_offset = align_offset + mem::size_of::<Self::Trailer>() as u32;
    (
      trailer,
      Some(arena.get_bytes(value_offset as usize, len as usize)),
      ValuePartPointer::new(offset, value_offset as u32, len),
    )
  }

  #[inline]
  fn align_offset(current_offset: u32) -> u32 {
    let alignment = mem::align_of::<Self::Trailer>() as u32;
    (current_offset + alignment - 1) & !(alignment - 1)
  }
}

pub(crate) trait NodePointer: Copy + core::fmt::Debug {
  type Node: Node;

  const NULL: Self;

  fn new(ptr: *mut u8, offset: u32) -> Self;

  #[inline]
  fn is_null(&self) -> bool {
    self.offset() == 0
  }

  fn offset(&self) -> u32;

  fn ptr(&self) -> *mut Self::Node;

  #[inline]
  unsafe fn tower<A: Allocator>(&self, arena: &A, idx: usize) -> &<Self::Node as Node>::Link {
    let tower_ptr_offset = self.offset() as usize
      + mem::size_of::<Self::Node>()
      + idx * mem::size_of::<<Self::Node as Node>::Link>();
    let tower_ptr = arena.get_pointer(tower_ptr_offset);
    &*tower_ptr.cast()
  }

  #[inline]
  unsafe fn write_tower<A: Allocator>(
    &self,
    arena: &A,
    idx: usize,
    prev_offset: u32,
    next_offset: u32,
  ) {
    let tower_ptr_offset = self.offset() as usize
      + mem::size_of::<Self::Node>()
      + idx * mem::size_of::<<Self::Node as Node>::Link>();
    let tower_ptr: *mut <Self::Node as Node>::Link = arena.get_pointer_mut(tower_ptr_offset).cast();
    *tower_ptr = Link::new(next_offset, prev_offset);
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
  unsafe fn next_offset<A: Allocator>(&self, arena: &A, idx: usize) -> u32;

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
  unsafe fn prev_offset<A: Allocator>(&self, arena: &A, idx: usize) -> u32;

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
  unsafe fn cas_prev_offset<A: Allocator>(
    &self,
    arena: &A,
    idx: usize,
    current: u32,
    new: u32,
    success: Ordering,
    failure: Ordering,
  ) -> Result<u32, u32>;

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
  unsafe fn cas_next_offset<A: Allocator>(
    &self,
    arena: &A,
    idx: usize,
    current: u32,
    new: u32,
    success: Ordering,
    failure: Ordering,
  ) -> Result<u32, u32>;

  /// ## Safety
  /// - the pointer must be valid
  unsafe fn as_ref(&self) -> &Self::Node;

  /// ## Safety
  /// - the pointer must be valid
  unsafe fn as_mut(&self) -> &mut Self::Node;
}

pub(crate) trait BytesRefMut {
  fn offset(&self) -> u32;

  fn capacity(&self) -> u32;

  fn memory_offset(&self) -> usize;

  fn memory_capacity(&self) -> usize;

  fn detach(&mut self);

  fn as_mut_ptr(&self) -> *mut u8;

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn flush(&self) -> std::io::Result<()>;
}

pub(crate) trait RefMut<T> {
  fn offset(&self) -> u32;

  fn memory_offset(&self) -> usize;

  fn memory_capacity(&self) -> usize;

  unsafe fn detach(&mut self);

  unsafe fn write(&mut self, value: T);

  fn as_mut_ptr(&mut self) -> NonNull<T>;
}

pub(crate) trait Header {
  fn new(magic_version: u16) -> Self;

  fn magic_version(&self) -> u16;

  fn max_version(&self) -> u64;

  fn min_version(&self) -> u64;

  fn height(&self) -> u8;

  fn len(&self) -> u32;

  fn increase_len(&self);

  fn update_max_version(&self, version: u64);

  fn update_min_version(&self, version: u64);

  fn compare_exchange_height_weak(
    &self,
    current: u8,
    new: u8,
    success: Ordering,
    failure: Ordering,
  ) -> Result<u8, u8>;
}

pub(crate) trait Allocator: Sized + Clone {
  type BytesRefMut<'a>: BytesRefMut
  where
    Self: 'a;
  type RefMut<'a, T>: RefMut<T>
  where
    Self: 'a;

  type Header: Header;

  type Node: Node<Trailer = Self::Trailer>;

  type Trailer: Trailer;

  fn allocated(&self) -> u32;

  fn capacity(&self) -> usize;

  fn data_offset(&self) -> usize;

  fn read_only(&self) -> bool;

  /// Returns the offset to the start of the ARENA.
  ///
  /// # Safety
  /// - `ptr` must be allocated by this ARENA.
  unsafe fn offset(&self, ptr: *const u8) -> usize;

  fn align_offset<T>(offset: u32) -> u32;

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
  unsafe fn alloc<T>(&self) -> Result<Self::RefMut<'_, T>, ArenaError>;

  /// Returns an aligned pointer to the memory at the given offset.
  ///
  /// # Safety
  /// - `offset..offset + mem::size_of::<T>() + padding` must be allocated memory.
  /// - `offset` must be less than the capacity of the ARENA.
  unsafe fn get_aligned_pointer<T>(&self, offset: usize) -> *const T;

  /// Returns a pointer to the memory at the given offset.
  ///
  /// # Safety
  /// - `offset` must be less than the capacity of the ARENA.
  unsafe fn get_pointer(&self, offset: usize) -> *const u8;

  /// Returns a pointer to the memory at the given offset.
  ///
  /// # Safety
  /// - `offset` must be less than the capacity of the ARENA.
  unsafe fn get_pointer_mut(&self, offset: usize) -> *mut u8;

  /// Returns a bytes slice from the ARENA.
  ///
  /// # Safety
  /// - `offset..offset + size` must be allocated memory.
  /// - `offset` must be less than the capacity of the ARENA.
  /// - `size` must be less than the capacity of the ARENA.
  /// - `offset + size` must be less than the capacity of the ARENA.
  unsafe fn get_bytes(&self, offset: usize, size: usize) -> &[u8];

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
  unsafe fn get_bytes_mut(&self, offset: usize, size: usize) -> &mut [u8];

  /// Deallocates the memory at the given offset and size, the `offset..offset + size` will be made to a segment,
  /// returns `true` if the deallocation is successful.
  ///
  /// # Safety
  /// - you must ensure the same `offset..offset + size` is not deallocated twice.
  /// - `offset` must be larger than the [`Self::data_offset`].
  /// - `offset + size` must be less than the [`Self::allocated`].
  unsafe fn dealloc(&self, offset: u32, size: u32) -> bool;

  /// Increases the discarded memory by `size`.
  fn increase_discarded(&self, size: u32);

  /// Returns the number of references to the Allocator.
  fn refs(&self) -> usize;

  fn fetch_vacant_key<'a, 'b: 'a, E>(
    &'a self,
    key_size: u32,
    key: impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>,
  ) -> Result<VacantBuffer<'a>, Either<E, Error>> {
    let (key_offset, key_size) = self
      .alloc_bytes(key_size)
      .map(|mut b| {
        b.detach();
        (b.offset(), b.capacity())
      })
      .map_err(|e| Either::Right(e.into()))?;

    let mut vk = unsafe {
      VacantBuffer::new(
        key_size as usize,
        key_offset as u32,
        self.get_bytes_mut(key_offset as usize, key_size as usize),
      )
    };
    key(&mut vk)
      .map_err(|e| {
        unsafe {
          self.dealloc(key_offset as u32, key_size as u32);
        }
        Either::Left(e)
      })
      .map(|_| vk)
  }

  #[inline]
  unsafe fn fill_vacant_key<'a, E>(
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
  unsafe fn fill_vacant_value<'a, E>(
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
  fn allocate_header(&self, magic_version: u16) -> Result<NonNull<Self::Header>, ArenaError> {
    // Safety: meta does not need to be dropped, and it is recoverable.
    unsafe {
      let mut meta = self.alloc::<Self::Header>()?;
      meta.detach();

      meta.write(Self::Header::new(magic_version));
      Ok(meta.as_mut_ptr())
    }
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
  ) -> Result<(<Self::Node as Node>::Pointer, Deallocator), Either<E, Error>> {
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
      node_ref.set_value_pointer(trailer_offset, value_size);
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

      Ok((
        NodePointer::new(node_ptr as _, node_offset as u32),
        deallocator,
      ))
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
  ) -> Result<(<Self::Node as Node>::Pointer, Deallocator), Either<E, Error>> {
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
      node_ref.set_value_pointer(trailer_offset, value_size);
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

      Ok((
        NodePointer::new(node_ptr as _, node_offset as u32),
        deallocator,
      ))
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
  ) -> Result<(<Self::Node as Node>::Pointer, Deallocator), Either<E, Error>> {
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
      node_ref.set_value_pointer(trailer_offset, value_size);
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

      Ok((
        NodePointer::new(node_ptr as _, node_offset as u32),
        deallocator,
      ))
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
  ) -> Result<(<Self::Node as Node>::Pointer, Deallocator), Either<E, Error>> {
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
      node_ref.set_value_pointer(trailer_offset, value_size);
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

      Ok((
        NodePointer::new(node_ptr as _, node_offset as u32),
        deallocator,
      ))
    }
  }

  fn allocate_full_node(
    &self,
    max_height: u8,
  ) -> Result<<Self::Node as Node>::Pointer, ArenaError> {
    // Safety: node, links and trailer do not need to be dropped, and they are recoverable.
    unsafe {
      let mut node = self.alloc_aligned_bytes::<Self::Node>(
        ((max_height as usize) * mem::size_of::<<Self::Node as Node>::Link>()) as u32,
      )?;

      // Safety: node and trailer do not need to be dropped.
      node.detach();

      let node_ptr = node.as_mut_ptr().cast::<Self::Node>();
      let node_offset = node.offset();

      let trailer_offset = if mem::size_of::<<Self::Node as Node>::Trailer>() != 0 {
        let mut trailer = self.alloc::<<Self::Node as Node>::Trailer>()?;
        trailer.detach();
        trailer.offset()
      } else {
        self.allocated()
      };

      let node = &mut *node_ptr;
      *node = <Self::Node as Node>::full(trailer_offset as u32, max_height);

      Ok(NodePointer::new(node_ptr as _, node_offset as u32))
    }
  }

  #[inline]
  fn allocate_and_update_value<'a, E>(
    &'a self,
    node: &Self::Node,
    trailer: <Self::Node as Node>::Trailer,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<(), Either<E, Error>> {
    let (value_size, f) = value_builder.into_components();
    let mut bytes = self
      .alloc_aligned_bytes::<<Self::Node as Node>::Trailer>(value_size)
      .map_err(|e| Either::Right(e.into()))?;
    let trailer_ptr = bytes.as_mut_ptr().cast::<<Self::Node as Node>::Trailer>();
    let trailer_offset = bytes.offset();
    let value_offset = trailer_offset as usize + mem::size_of::<<Self::Node as Node>::Trailer>();

    let mut oval = VacantBuffer::new(value_size as usize, value_offset as u32, unsafe {
      self.get_bytes_mut(value_offset, value_size as usize)
    });
    f(&mut oval).map_err(Either::Left)?;

    let remaining = oval.remaining();
    let mut discard = 0;
    if remaining != 0
      && unsafe { !self.dealloc((value_offset + oval.len()) as u32, remaining as u32) }
    {
      discard += remaining;
    }

    bytes.detach();
    unsafe {
      trailer_ptr.write(trailer);
    }

    if discard != 0 {
      self.increase_discarded(discard as u32);
    }

    let (_, old_len) = node.value_pointer().swap(trailer_offset as u32, value_size);
    if old_len != <<Self::Node as Node>::ValuePointer as ValuePointer>::REMOVE {
      self.increase_discarded(old_len);
    }

    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    {
      if self.is_on_disk_and_mmap() {
        bytes.flush().map_err(|e| Either::Right(e.into()))?;
      }
    }

    Ok(())
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(windows)))]
  unsafe fn munlock(&self, offset: usize, size: usize) -> std::io::Result<()>;

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn is_on_disk_and_mmap(&self) -> bool;

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn is_ondisk(&self) -> bool;

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn is_mmap(&self) -> bool;

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn flush_range(&self, offset: usize, size: usize) -> std::io::Result<()>;

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
