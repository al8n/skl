use dbutils::buffer::VacantBuffer;
use either::Either;
use rarena_allocator::{Allocator as ArenaAllocator, Buffer, BytesRefMut};

use super::{
  decode_key_size_and_height, encode_key_size_and_height,
  error::{ArenaError, Error},
  options::Options,
  types::{internal::ValuePointer as ValuePointerType, Height, KeyBuilder, ValueBuilder},
  Version, REMOVE,
};

use core::{marker::PhantomData, mem, ptr::NonNull, sync::atomic::Ordering};

pub trait Allocator: Sealed {}

impl<T> Allocator for T where T: Sealed {}

pub(crate) use sealed::*;

mod sealed {
  use core::{ops::Deref, ptr};

  use among::Among;

  use crate::internal::Flags;

  use super::*;

  pub struct Pointer {
    pub(crate) offset: u32,
    pub(crate) size: u32,
    #[allow(dead_code)]
    pub(crate) height: Option<u8>,
  }

  impl Pointer {
    #[inline]
    pub(crate) const fn new(offset: u32, size: u32) -> Self {
      Self {
        offset,
        size,
        height: None,
      }
    }
  }

  pub struct Deallocator {
    pub(crate) node: Option<Pointer>,
    pub(crate) key: Option<Pointer>,
    pub(crate) value: Option<Pointer>,
  }

  impl Deallocator {
    #[inline]
    pub fn dealloc<A: Sealed>(self, arena: &A) {
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
    pub fn dealloc_node_and_key<A: Sealed>(self, arena: &A) {
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
    pub fn dealloc_key_by_ref<A: Sealed>(&mut self, arena: &A) {
      if let Some(ptr) = self.key.take() {
        unsafe {
          arena.dealloc(ptr.offset, ptr.size);
        }
      }
    }
  }

  pub trait ValuePointer {
    /// The tombstone value.
    const REMOVE: u32;

    fn swap(&self, offset: u32, size: u32) -> (u32, u32);

    fn load(&self) -> (u32, u32);

    fn compare_remove(
      &self,
      success: Ordering,
      failure: Ordering,
    ) -> Result<(u32, u32), (u32, u32)>;

    #[inline]
    fn is_removed(&self) -> bool {
      self.load().1 == Self::REMOVE
    }
  }

  pub trait Link {
    fn new(next_offset: u32, prev_offset: u32) -> Self;

    fn store_next_offset(&self, offset: u32, ordering: Ordering);

    fn store_prev_offset(&self, offset: u32, ordering: Ordering);
  }

  #[doc(hidden)]
  pub trait WithVersion: Node {}

  #[doc(hidden)]
  pub trait WithoutVersion: Node {}

  pub trait Node: Sized + core::fmt::Debug {
    type Link: Link;
    type ValuePointer: ValuePointer;
    type Pointer: NodePointer<Node = Self>;

    fn full(value_offset: u32, max_height: u8) -> Self;

    fn flags() -> Flags;

    #[inline]
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

    #[inline]
    fn clear_value<A: Allocator>(
      &self,
      arena: &A,
      success: Ordering,
      failure: Ordering,
    ) -> Result<(), (u32, u32)> {
      self
        .value_pointer()
        .compare_remove(success, failure)
        .map(|(_, old_len)| {
          if old_len != REMOVE {
            arena.increase_discarded(old_len);
          }
        })
    }

    fn set_key_size_and_height(&mut self, key_size_and_height: u32);

    fn set_key_offset(&mut self, key_offset: u32);

    fn set_version(&mut self, version: Version);

    /// ## Safety
    ///
    /// - The caller must ensure that the node is allocated by the arena.
    #[inline]
    unsafe fn get_value<'a, 'b: 'a, A: Allocator>(&'a self, arena: &'b A) -> Option<&'b [u8]> {
      let (offset, len) = self.value_pointer().load();

      if len == <Self::ValuePointer as ValuePointer>::REMOVE {
        return None;
      }

      Some(arena.get_bytes(offset as usize, len as usize))
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
      if len == <Self::ValuePointer as ValuePointer>::REMOVE {
        return None;
      }

      Some(arena.get_bytes(offset as usize, len as usize))
    }

    /// ## Safety
    ///
    /// - The caller must ensure that the node is allocated by the arena.
    #[inline]
    unsafe fn get_value_with_pointer<'a, 'b: 'a, A: Allocator>(
      &'a self,
      arena: &'b A,
    ) -> (Option<&'b [u8]>, ValuePointerType) {
      let (offset, len) = self.value_pointer().load();

      if len == <Self::ValuePointer as ValuePointer>::REMOVE {
        return (None, ValuePointerType::new(offset, len));
      }

      (
        Some(arena.get_bytes(offset as usize, len as usize)),
        ValuePointerType::new(offset, len),
      )
    }
  }

  pub trait NodePointer: Copy + core::fmt::Debug {
    type Node: Node;

    const NULL: Self;

    fn new(offset: u32, ptr: NonNull<u8>) -> Self;

    #[inline]
    fn is_null(&self) -> bool {
      self.offset() == 0
    }

    fn offset(&self) -> u32;

    #[inline]
    unsafe fn tower<A: Sealed>(&self, arena: &A, idx: usize) -> &<Self::Node as Node>::Link {
      let tower_ptr_offset = self.offset() as usize
        + mem::size_of::<Self::Node>()
        + idx * mem::size_of::<<Self::Node as Node>::Link>();
      let tower_ptr = arena.get_pointer(tower_ptr_offset);
      &*tower_ptr.cast()
    }

    #[inline]
    unsafe fn write_tower<A: Sealed>(
      &self,
      arena: &A,
      idx: usize,
      prev_offset: u32,
      next_offset: u32,
    ) {
      let tower_ptr_offset = self.offset() as usize
        + mem::size_of::<Self::Node>()
        + idx * mem::size_of::<<Self::Node as Node>::Link>();
      let tower_ptr: *mut <Self::Node as Node>::Link =
        arena.get_pointer_mut(tower_ptr_offset).cast();
      *tower_ptr = Link::new(next_offset, prev_offset);
    }

    /// ## Safety
    ///
    /// - The caller must ensure that the node is allocated by the arena.
    /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
    unsafe fn next_offset<A: Sealed>(&self, arena: &A, idx: usize) -> u32;

    /// ## Safety
    ///
    /// - The caller must ensure that the node is allocated by the arena.
    /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
    unsafe fn prev_offset<A: Sealed>(&self, arena: &A, idx: usize) -> u32;

    /// ## Safety
    ///
    /// - The caller must ensure that the node is allocated by the arena.
    /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
    unsafe fn cas_prev_offset<A: Sealed>(
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
    unsafe fn cas_next_offset<A: Sealed>(
      &self,
      arena: &A,
      idx: usize,
      current: u32,
      new: u32,
      success: Ordering,
      failure: Ordering,
    ) -> Result<u32, u32>;

    // /// ## Safety
    // /// - the pointer must be valid
    // unsafe fn as_ref<A: Sealed>(&self, arena: &A) -> &Self::Node;

    // /// ## Safety
    // /// - the pointer must be valid
    // unsafe fn as_mut<A: Sealed>(&self, arena: &A) -> &mut Self::Node;

    fn value_pointer(&self) -> &<Self::Node as Node>::ValuePointer;

    #[inline]
    fn update_value<A: Allocator>(&self, arena: &A, offset: u32, value_size: u32) {
      let (_, old_len) = NodePointer::value_pointer(self).swap(offset, value_size);
      if old_len != <Self::Node as Node>::ValuePointer::REMOVE {
        arena.increase_discarded(old_len);
      }
    }

    #[inline]
    fn clear_value<A: super::Allocator>(
      &self,
      arena: &A,
      success: Ordering,
      failure: Ordering,
    ) -> Result<(), (u32, u32)> {
      NodePointer::value_pointer(self)
        .compare_remove(success, failure)
        .map(|(_, old_len)| {
          if old_len != REMOVE {
            arena.increase_discarded(old_len);
          }
        })
    }

    #[inline]
    fn is_removed(&self) -> bool {
      self.value_pointer().is_removed()
    }

    #[allow(dead_code)]
    fn set_key_size_and_height(&self, key_size_and_height: u32);

    #[allow(dead_code)]
    fn set_key_offset(&self, key_offset: u32);

    fn key_size_and_height(&self) -> u32;

    fn key_offset(&self) -> u32;

    fn version(&self) -> Version;

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
    #[inline]
    unsafe fn get_key<'a, 'b: 'a, A: Allocator>(&'a self, arena: &'b A) -> &'b [u8] {
      arena.get_bytes(self.key_offset() as usize, self.key_size() as usize)
    }

    /// ## Safety
    ///
    /// - The caller must ensure that the node is allocated by the arena.
    #[inline]
    unsafe fn get_value<'a, 'b: 'a, A: Allocator>(&'a self, arena: &'b A) -> Option<&'b [u8]> {
      let (offset, len) = self.value_pointer().load();

      if len == <<Self::Node as Node>::ValuePointer as ValuePointer>::REMOVE {
        return None;
      }

      Some(arena.get_bytes(offset as usize, len as usize))
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
      if len == <<Self::Node as Node>::ValuePointer as ValuePointer>::REMOVE {
        return None;
      }

      Some(arena.get_bytes(offset as usize, len as usize))
    }

    /// ## Safety
    ///
    /// - The caller must ensure that the node is allocated by the arena.
    #[inline]
    unsafe fn get_value_with_pointer<'a, 'b: 'a, A: Allocator>(
      &'a self,
      arena: &'b A,
    ) -> (Option<&'b [u8]>, ValuePointerType) {
      let (offset, len) = self.value_pointer().load();
      if len == <<Self::Node as Node>::ValuePointer as ValuePointer>::REMOVE {
        return (None, ValuePointerType::new(offset, len));
      }

      (
        Some(arena.get_bytes(offset as usize, len as usize)),
        ValuePointerType::new(offset, len),
      )
    }

    /// ## Safety
    ///
    /// - The caller must ensure that the node is allocated by the arena.
    #[inline]
    unsafe fn get_value_pointer<A: Allocator>(&self) -> ValuePointerType {
      let (offset, len) = self.value_pointer().load();

      if len == <<Self::Node as Node>::ValuePointer as ValuePointer>::REMOVE {
        return ValuePointerType::new(offset, len);
      }

      ValuePointerType::new(offset, len)
    }
  }

  pub trait Header: core::fmt::Debug {
    fn new(magic_version: u16) -> Self;

    fn magic_version(&self) -> u16;

    fn maximum_version(&self) -> u64;

    fn minimum_version(&self) -> u64;

    fn height(&self) -> u8;

    fn flags(&self) -> Flags;

    fn len(&self) -> u32;

    fn increase_len(&self);

    fn update_maximum_version(&self, version: u64);

    fn update_minimum_version(&self, version: u64);

    fn compare_exchange_height_weak(
      &self,
      current: u8,
      new: u8,
      success: Ordering,
      failure: Ordering,
    ) -> Result<u8, u8>;
  }

  impl<T: Allocator> AllocatorExt for T {}

  pub trait AllocatorExt: Allocator {
    /// Checks if the arena has enough capacity to store the skiplist,
    /// and returns the data offset.
    #[inline]
    fn check_capacity(&self, max_height: u8) -> Result<u32, Error> {
      let offset = self.data_offset();

      let meta_end = if self.options().unify() {
        let alignment = mem::align_of::<Self::Header>();
        let meta_offset = (offset + alignment - 1) & !(alignment - 1);
        meta_offset + mem::size_of::<Self::Header>()
      } else {
        offset
      };

      let alignment = mem::align_of::<Self::Node>();
      let head_offset = (meta_end + alignment - 1) & !(alignment - 1);
      let head_end = head_offset
        + mem::size_of::<Self::Node>()
        + mem::size_of::<<Self::Node as Node>::Link>() * max_height as usize;

      let tail_offset = (head_end + alignment - 1) & !(alignment - 1);
      let tail_end = tail_offset
        + mem::size_of::<Self::Node>()
        + mem::size_of::<<Self::Node as Node>::Link>() * max_height as usize;
      if tail_end > self.capacity() {
        return Err(Error::ArenaTooSmall);
      }

      Ok(tail_end as u32)
    }

    #[inline]
    fn get_pointers(
      &self,
    ) -> (
      NonNull<Self::Header>,
      <Self::Node as Node>::Pointer,
      <Self::Node as Node>::Pointer,
    ) {
      unsafe {
        let offset = self.data_offset();
        let meta = self.get_aligned_pointer::<Self::Header>(offset);

        let offset = self.offset(meta as _) + mem::size_of::<Self::Header>();
        let head_ptr = self.get_aligned_pointer::<Self::Node>(offset);
        let head_offset = self.offset(head_ptr as _);
        let head = <<Self::Node as Node>::Pointer as NodePointer>::new(
          head_offset as u32,
          NonNull::new_unchecked(head_ptr as _),
        );

        let (value_offset, _) = head.value_pointer().load();
        let offset = value_offset;
        let tail_ptr = self.get_aligned_pointer::<Self::Node>(offset as usize);
        let tail_offset = self.offset(tail_ptr as _);
        let tail = <<Self::Node as Node>::Pointer as NodePointer>::new(
          tail_offset as u32,
          NonNull::new_unchecked(tail_ptr as _),
        );
        (NonNull::new_unchecked(meta as _), head, tail)
      }
    }
  }

  pub trait Sealed:
    Sized + Clone + core::fmt::Debug + core::ops::Deref<Target = Self::Allocator>
  {
    type Header: Header;

    type Node: Node;

    type Allocator: ArenaAllocator;

    fn options(&self) -> &Options;

    #[inline]
    fn reserved_bytes(&self) -> usize {
      ArenaAllocator::reserved_bytes(Deref::deref(self))
    }

    #[inline]
    fn reserved_slice(&self) -> &[u8] {
      ArenaAllocator::reserved_slice(Deref::deref(self))
    }

    #[inline]
    unsafe fn reserved_slice_mut(&self) -> &mut [u8] {
      ArenaAllocator::reserved_slice_mut(Deref::deref(self))
    }

    #[inline]
    fn unify(&self) -> bool {
      ArenaAllocator::unify(Deref::deref(self))
    }

    #[inline]
    fn prefix_slice(&self) -> &[u8] {
      let arena = Deref::deref(self);

      // Safety: the slice must within range
      unsafe { arena.get_bytes(0, self.data_offset()) }
    }

    fn new(arena: Self::Allocator, opts: Options) -> Self;

    #[inline]
    fn align_offset<T>(offset: u32) -> u32 {
      rarena_allocator::align_offset::<T>(offset)
    }

    fn fetch_vacant_key<'a, 'b: 'a, E>(
      &'a self,
      key_size: u32,
      key: impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>,
    ) -> Result<(u32, VacantBuffer<'a>), Either<E, Error>> {
      let (key_offset, key_size) = self
        .alloc_bytes(key_size)
        .map(|mut b| {
          unsafe {
            b.detach();
          }
          (b.offset(), b.capacity())
        })
        .map_err(|e| Either::Right(e.into()))?;

      let mut vk = unsafe {
        VacantBuffer::new(
          key_size,
          NonNull::new_unchecked(self.get_pointer_mut(key_offset)),
        )
      };
      key(&mut vk)
        .map_err(|e| {
          unsafe {
            self.dealloc(key_offset as u32, key_size as u32);
          }
          Either::Left(e)
        })
        .map(|_| (key_offset as u32, vk))
    }

    #[inline]
    unsafe fn fill_vacant_key<'a, E>(
      &'a self,
      size: u32,
      offset: u32,
      f: impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>,
    ) -> Result<(u32, Pointer), E> {
      let buf = self.get_pointer_mut(offset as usize);
      let mut oval = VacantBuffer::new(size as usize, NonNull::new_unchecked(buf));
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
      f: impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>,
    ) -> Result<(u32, Pointer), E> {
      let buf = self.get_pointer_mut(offset as usize);
      let mut oval = VacantBuffer::new(size as usize, NonNull::new_unchecked(buf));
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
    fn allocate_pure_node(
      &self,
      height: u32,
    ) -> Result<BytesRefMut<'_, Self::Allocator>, ArenaError> {
      self.alloc_aligned_bytes::<Self::Node>(
        height * mem::size_of::<<Self::Node as Node>::Link>() as u32,
      )
    }

    /// Allocates a `Node`, key and value
    fn allocate_entry_node<'a, 'b: 'a, KE, VE>(
      &'a self,
      version: Version,
      height: u32,
      key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), KE>>,
      value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), VE>>,
    ) -> Result<(<Self::Node as Node>::Pointer, Deallocator), Among<KE, VE, Error>> {
      let (key_size, kf) = key_builder.into_components();
      let (value_size, vf) = value_builder.into_components();

      unsafe {
        let mut node = self
          .allocate_pure_node(height)
          .map_err(|e| Among::Right(e.into()))?;
        let node_ptr = node.as_mut_ptr().cast::<Self::Node>();
        let node_offset = node.offset();

        let mut key = self
          .alloc_bytes(key_size as u32)
          .map_err(|e| Among::Right(e.into()))?;
        let key_offset = key.offset();
        let key_cap = key.capacity();
        let mut value = self
          .alloc_bytes(value_size as u32)
          .map_err(|e| Among::Right(e.into()))?;
        let value_offset = value.offset();

        // Safety: the node is well aligned
        let node_ref = &mut *node_ptr;
        node_ref.set_value_pointer(value_offset as u32, value_size as u32);
        node_ref.set_key_offset(key_offset as u32);
        node_ref.set_key_size_and_height(encode_key_size_and_height(key_cap as u32, height as u8));
        node_ref.set_version(version);

        key.detach();
        let (_, key_deallocate_info) = self
          .fill_vacant_key(key_cap as u32, key_offset as u32, kf)
          .map_err(Among::Left)?;
        value.detach();
        let (_, value_deallocate_info) = self
          .fill_vacant_value(value_offset as u32, value_size as u32, vf)
          .map_err(Among::Middle)?;
        node.detach();

        let deallocator = Deallocator {
          node: Some(Pointer::new(node_offset as u32, node.capacity() as u32)),
          key: Some(key_deallocate_info),
          value: Some(value_deallocate_info),
        };

        Ok((
          NodePointer::new(node_offset as u32, NonNull::new_unchecked(node_ptr as _)),
          deallocator,
        ))
      }
    }

    /// Allocates a tombstone `Node`
    fn allocate_tombstone_node<'a, 'b: 'a, E>(
      &'a self,
      version: Version,
      height: u32,
      key_offset: u32,
      key_size: usize,
    ) -> Result<(<Self::Node as Node>::Pointer, Deallocator), Either<E, Error>> {
      let key_size = key_size as u32;

      unsafe {
        let mut node = self
          .alloc_aligned_bytes::<Self::Node>(
            height * mem::size_of::<<Self::Node as Node>::Link>() as u32,
          )
          .map_err(|e| Either::Right(e.into()))?;
        let node_ptr = node.as_mut_ptr().cast::<Self::Node>();
        let node_offset = node.offset();

        // Safety: the node is well aligned
        let node_ref = &mut *node_ptr;
        node_ref.set_value_pointer(
          node_offset as u32,
          <<Self::Node as Node>::ValuePointer>::REMOVE,
        );
        node_ref.set_key_offset(key_offset);
        node_ref.set_key_size_and_height(encode_key_size_and_height(key_size, height as u8));
        node_ref.set_version(version);

        node.detach();

        let deallocator = Deallocator {
          node: Some(Pointer::new(node_offset as u32, node.capacity() as u32)),
          key: None,
          value: None,
        };

        Ok((
          NodePointer::new(node_offset as u32, NonNull::new_unchecked(node_ptr as _)),
          deallocator,
        ))
      }
    }

    /// Allocates a `Node`, key
    fn allocate_tombstone_node_with_key_builder<'a, 'b: 'a, E>(
      &'a self,
      version: Version,
      height: u32,
      key_size: usize,
      kf: impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>,
    ) -> Result<(<Self::Node as Node>::Pointer, Deallocator), Either<E, Error>> {
      let key_size = key_size as u32;

      unsafe {
        let mut node = self
          .alloc_aligned_bytes::<Self::Node>(
            height * mem::size_of::<<Self::Node as Node>::Link>() as u32,
          )
          .map_err(|e| Either::Right(e.into()))?;
        let node_ptr = node.as_mut_ptr().cast::<Self::Node>();
        let node_offset = node.offset();
        let value_offset = node_offset + node.capacity();

        let mut key = self
          .alloc_bytes(key_size)
          .map_err(|e| Either::Right(e.into()))?;
        let key_offset = key.offset();
        let key_cap = key.capacity();

        // Safety: the node is well aligned
        let node_ref = &mut *node_ptr;
        node_ref.set_value_pointer(
          value_offset as u32,
          <Self::Node as Node>::ValuePointer::REMOVE,
        );
        node_ref.set_key_offset(key_offset as u32);
        node_ref.set_key_size_and_height(encode_key_size_and_height(key_cap as u32, height as u8));
        node_ref.set_version(version);

        key.detach();
        let (_, key_deallocate_info) = self
          .fill_vacant_key(key_cap as u32, key_offset as u32, kf)
          .map_err(Either::Left)?;

        node.detach();

        let deallocator = Deallocator {
          node: Some(Pointer::new(node_offset as u32, node.capacity() as u32)),
          key: Some(key_deallocate_info),
          value: None,
        };

        Ok((
          NodePointer::new(node_offset as u32, NonNull::new_unchecked(node_ptr as _)),
          deallocator,
        ))
      }
    }

    /// Allocates a `Node`, value
    fn allocate_value_node<'a, 'b: 'a, E>(
      &'a self,
      version: Version,
      height: u32,
      key_size: usize,
      key_offset: u32,
      value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    ) -> Result<(<Self::Node as Node>::Pointer, Deallocator), Either<E, Error>> {
      let (value_size, vf) = value_builder.into_components();

      let value_size = value_size as u32;

      unsafe {
        let mut node = self
          .alloc_aligned_bytes::<Self::Node>(
            height * mem::size_of::<<Self::Node as Node>::Link>() as u32,
          )
          .map_err(|e| Either::Right(e.into()))?;
        let node_ptr = node.as_mut_ptr().cast::<Self::Node>();
        let node_offset = node.offset();

        let mut value = self
          .alloc_bytes(value_size)
          .map_err(|e| Either::Right(e.into()))?;
        let value_offset = value.offset();

        // Safety: the node is well aligned
        let node_ref = &mut *node_ptr;
        node_ref.set_value_pointer(value_offset as u32, value_size);
        node_ref.set_key_offset(key_offset);
        node_ref.set_key_size_and_height(encode_key_size_and_height(key_size as u32, height as u8));
        node_ref.set_version(version);

        value.detach();
        let (_, value_deallocate_info) = self
          .fill_vacant_value(value_offset as u32, value_size, vf)
          .map_err(Either::Left)?;

        node.detach();

        let deallocator = Deallocator {
          node: Some(Pointer::new(node_offset as u32, node.capacity() as u32)),
          key: None,
          value: Some(value_deallocate_info),
        };

        Ok((
          NodePointer::new(node_offset as u32, NonNull::new_unchecked(node_ptr as _)),
          deallocator,
        ))
      }
    }

    fn allocate_full_node(
      &self,
      max_height: u8,
    ) -> Result<<Self::Node as Node>::Pointer, ArenaError> {
      // Safety: node and links do not need to be dropped, and they are recoverable.
      unsafe {
        let mut node = self.alloc_aligned_bytes::<Self::Node>(
          ((max_height as usize) * mem::size_of::<<Self::Node as Node>::Link>()) as u32,
        )?;

        // Safety: node do not need to be dropped.
        node.detach();
        let node_offset = node.offset();
        let value_offset = self.allocated();

        let node_ptr = node.as_mut_ptr().cast::<Self::Node>();
        let full_node = <Self::Node as Node>::full(value_offset as u32, max_height);
        ptr::write(node_ptr, full_node);

        Ok(NodePointer::new(
          node_offset as u32,
          NonNull::new_unchecked(node_ptr as _),
        ))
      }
    }

    #[inline]
    fn allocate_and_update_value<'a, E>(
      &'a self,
      node: &<Self::Node as Node>::Pointer,
      value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    ) -> Result<(), Either<E, Error>> {
      let (value_size, f) = value_builder.into_components();
      let value_size = value_size as u32;
      let mut bytes = self
        .alloc_bytes(value_size)
        .map_err(|e| Either::Right(e.into()))?;
      let value_offset = bytes.offset();

      let mut oval = unsafe {
        VacantBuffer::new(
          value_size as usize,
          NonNull::new_unchecked(self.get_pointer_mut(value_offset)),
        )
      };
      f(&mut oval).map_err(Either::Left)?;

      let remaining = oval.remaining();
      let mut discard = 0;
      if remaining != 0
        && unsafe { !self.dealloc((value_offset + oval.len()) as u32, remaining as u32) }
      {
        discard += remaining;
      }

      unsafe {
        bytes.detach();
      }

      if discard != 0 {
        self.increase_discarded(discard as u32);
      }

      let (_, old_len) = node.value_pointer().swap(value_offset as u32, value_size);
      if old_len != <<Self::Node as Node>::ValuePointer as ValuePointer>::REMOVE {
        self.increase_discarded(old_len);
      }

      Ok(())
    }

    fn max_key_size(&self) -> usize;

    fn max_value_size(&self) -> usize;

    fn max_height(&self) -> Height;
  }
}

/// Generic ARENA allocator
#[derive(Debug)]
pub struct GenericAllocator<H, N, A> {
  arena: A,
  opts: Options,
  _m: PhantomData<(H, N)>,
}

impl<H, N, A: Clone> Clone for GenericAllocator<H, N, A> {
  fn clone(&self) -> Self {
    Self {
      arena: self.arena.clone(),
      opts: self.opts,
      _m: PhantomData,
    }
  }
}

impl<H, N, A> core::ops::Deref for GenericAllocator<H, N, A> {
  type Target = A;

  fn deref(&self) -> &A {
    &self.arena
  }
}

impl<H: Header, N: Node, A: ArenaAllocator + core::fmt::Debug> Sealed
  for GenericAllocator<H, N, A>
{
  type Header = H;

  type Node = N;

  type Allocator = A;

  #[inline]
  fn options(&self) -> &Options {
    &self.opts
  }

  #[inline]
  fn new(arena: Self::Allocator, opts: Options) -> Self {
    Self {
      arena,
      opts,
      _m: PhantomData,
    }
  }

  #[inline]
  fn max_key_size(&self) -> usize {
    self.opts.max_key_size().into()
  }

  #[inline]
  fn max_value_size(&self) -> usize {
    self.opts.max_value_size() as usize
  }

  #[inline]
  fn max_height(&self) -> Height {
    self.opts.max_height()
  }
}
