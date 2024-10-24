use either::Either;
use rarena_allocator::{Allocator as ArenaAllocator, Buffer, BytesRefMut};

use super::*;

use core::{marker::PhantomData, mem, ptr::NonNull, sync::atomic::Ordering};

pub trait Allocator: Sealed {}

impl<T> Allocator for T where T: Sealed {}

pub(crate) use sealed::*;

mod sealed {
  use core::{ops::Deref, ptr};

  use among::Among;

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

  #[derive(Debug)]
  pub struct ValuePartPointer<T> {
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
  pub trait WithTrailer: Node {}

  #[doc(hidden)]
  pub trait WithVersion: Node {}

  pub trait Node: Sized + core::fmt::Debug {
    type Link: Link;
    type Trailer: Trailer;
    type ValuePointer: ValuePointer;
    type Pointer: NodePointer<Node = Self>;

    fn full(value_offset: u32, max_height: u8) -> Self;

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
      if len == <Self::ValuePointer as ValuePointer>::REMOVE {
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
      if mem::size_of::<Self::Trailer>() == 0 {
        return dangling_zst_ref();
      }

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
      if mem::size_of::<Self::Trailer>() == 0 {
        return dangling_zst_ref();
      }

      &*arena.get_aligned_pointer(offset as usize)
    }

    /// ## Safety
    ///
    /// - The caller must ensure that the node is allocated by the arena.
    #[inline]
    unsafe fn get_value_and_trailer_with_pointer<'a, 'b: 'a, A: Allocator>(
      &'a self,
      arena: &'b A,
    ) -> (Option<&'b [u8]>, ValuePartPointer<Self::Trailer>) {
      let (offset, len) = self.value_pointer().load();

      let align_offset = A::align_offset::<Self::Trailer>(offset);

      if len == <Self::ValuePointer as ValuePointer>::REMOVE {
        return (
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
        Some(arena.get_bytes(value_offset as usize, len as usize)),
        ValuePartPointer::new(offset, value_offset, len),
      )
    }

    #[inline]
    fn align_offset(current_offset: u32) -> u32 {
      let alignment = mem::align_of::<Self::Trailer>() as u32;
      (current_offset + alignment - 1) & !(alignment - 1)
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
      let align_offset = Self::align_offset(offset);
      Some(arena.get_bytes(
        align_offset as usize + mem::size_of::<<Self::Node as Node>::Trailer>(),
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
      if len == <<Self::Node as Node>::ValuePointer as ValuePointer>::REMOVE {
        return None;
      }

      Some(arena.get_bytes(offset as usize, len as usize))
    }

    #[inline]
    fn trailer_offset_and_value_size(&self) -> ValuePartPointer<<Self::Node as Node>::Trailer> {
      let (offset, len) = self.value_pointer().load();
      let align_offset = Self::align_offset(offset);
      ValuePartPointer::new(
        align_offset,
        align_offset + mem::size_of::<<Self::Node as Node>::Trailer>() as u32,
        len,
      )
    }

    #[inline]
    unsafe fn get_trailer<'a, 'b: 'a, A: Allocator>(
      &'a self,
      arena: &'b A,
    ) -> &'b <Self::Node as Node>::Trailer {
      if mem::size_of::<<Self::Node as Node>::Trailer>() == 0 {
        return dangling_zst_ref();
      }

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
    ) -> &'b <Self::Node as Node>::Trailer {
      if mem::size_of::<<Self::Node as Node>::Trailer>() == 0 {
        return dangling_zst_ref();
      }

      &*arena.get_aligned_pointer(offset as usize)
    }

    /// ## Safety
    ///
    /// - The caller must ensure that the node is allocated by the arena.
    #[inline]
    unsafe fn get_value_and_trailer_with_pointer<'a, 'b: 'a, A: Allocator>(
      &'a self,
      arena: &'b A,
    ) -> (
      Option<&'b [u8]>,
      ValuePartPointer<<Self::Node as Node>::Trailer>,
    ) {
      let (offset, len) = self.value_pointer().load();

      let align_offset = A::align_offset::<<Self::Node as Node>::Trailer>(offset);

      if len == <<Self::Node as Node>::ValuePointer as ValuePointer>::REMOVE {
        return (
          None,
          ValuePartPointer::new(
            offset,
            align_offset + mem::size_of::<<Self::Node as Node>::Trailer>() as u32,
            len,
          ),
        );
      }

      let value_offset = align_offset + mem::size_of::<<Self::Node as Node>::Trailer>() as u32;
      (
        Some(arena.get_bytes(value_offset as usize, len as usize)),
        ValuePartPointer::new(offset, value_offset, len),
      )
    }

    /// ## Safety
    ///
    /// - The caller must ensure that the node is allocated by the arena.
    #[inline]
    unsafe fn get_value_pointer<A: Allocator>(
      &self,
    ) -> ValuePartPointer<<Self::Node as Node>::Trailer> {
      let (offset, len) = self.value_pointer().load();

      let align_offset = A::align_offset::<<Self::Node as Node>::Trailer>(offset);

      if len == <<Self::Node as Node>::ValuePointer as ValuePointer>::REMOVE {
        return ValuePartPointer::new(
          offset,
          align_offset + mem::size_of::<<Self::Node as Node>::Trailer>() as u32,
          len,
        );
      }

      let value_offset = align_offset + mem::size_of::<<Self::Node as Node>::Trailer>() as u32;
      ValuePartPointer::new(offset, value_offset, len)
    }

    #[inline]
    fn align_offset(current_offset: u32) -> u32 {
      let alignment = mem::align_of::<<Self::Node as Node>::Trailer>() as u32;
      (current_offset + alignment - 1) & !(alignment - 1)
    }
  }

  pub trait Header: core::fmt::Debug {
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

  impl<T: Allocator> AllocatorExt for T {}

  pub trait AllocatorExt: Allocator {
    /// Checks if the arena has enough capacity to store the skiplist,
    /// and returns the data offset.
    #[inline]
    fn check_capacity(&self, max_height: u8) -> Result<u32, Error> {
      let offset = self.data_offset();

      let alignment = mem::align_of::<Self::Header>();
      let meta_offset = (offset + alignment - 1) & !(alignment - 1);
      let meta_end = meta_offset + mem::size_of::<Self::Header>();

      let alignment = mem::align_of::<Self::Node>();
      let head_offset = (meta_end + alignment - 1) & !(alignment - 1);
      let head_end = head_offset
        + mem::size_of::<Self::Node>()
        + mem::size_of::<<Self::Node as Node>::Link>() * max_height as usize;

      let trailer_alignment = mem::align_of::<Self::Trailer>();
      let trailer_size = mem::size_of::<Self::Trailer>();
      let trailer_end = if trailer_size != 0 {
        let trailer_offset = (head_end + trailer_alignment - 1) & !(trailer_alignment - 1);
        trailer_offset + trailer_size
      } else {
        head_end
      };

      let tail_offset = (trailer_end + alignment - 1) & !(alignment - 1);
      let tail_end = tail_offset
        + mem::size_of::<Self::Node>()
        + mem::size_of::<<Self::Node as Node>::Link>() * max_height as usize;
      let trailer_end = if trailer_size != 0 {
        let trailer_offset = (tail_end + trailer_alignment - 1) & !(trailer_alignment - 1);
        trailer_offset + trailer_size
      } else {
        tail_end
      };
      if trailer_end > self.capacity() {
        return Err(Error::ArenaTooSmall);
      }

      Ok(trailer_end as u32)
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

        let (trailer_offset, _) = head.value_pointer().load();
        let offset = trailer_offset as usize + mem::size_of::<Self::Trailer>();
        let tail_ptr = self.get_aligned_pointer::<Self::Node>(offset);
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

    type Node: Node<Trailer = Self::Trailer>;

    type Trailer: Trailer;

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
      value_size: u32,
      value_offset: u32,
      f: impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>,
    ) -> Result<(u32, Pointer), E> {
      let buf = self.get_pointer_mut(value_offset as usize);
      let mut oval = VacantBuffer::new(value_size as usize, NonNull::new_unchecked(buf));
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
    fn allocate_pure_node(
      &self,
      height: u32,
    ) -> Result<BytesRefMut<'_, Self::Allocator>, ArenaError> {
      self.alloc_aligned_bytes::<Self::Node>(
        height * mem::size_of::<<Self::Node as Node>::Link>() as u32,
      )
    }

    /// Allocates a `Node`, key, trailer and value
    fn allocate_entry_node<'a, 'b: 'a, KE, VE>(
      &'a self,
      version: Version,
      height: u32,
      trailer: <Self::Node as Node>::Trailer,
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
        let mut trailer_and_value = self
          .alloc_aligned_bytes::<<Self::Node as Node>::Trailer>(value_size as u32)
          .map_err(|e| Among::Right(e.into()))?;
        let trailer_offset = trailer_and_value.offset();
        let trailer_ptr = trailer_and_value
          .as_mut_ptr()
          .cast::<<Self::Node as Node>::Trailer>();
        trailer_ptr.write(trailer);

        let value_offset =
          (trailer_offset + mem::size_of::<<Self::Node as Node>::Trailer>()) as u32;

        // Safety: the node is well aligned
        let node_ref = &mut *node_ptr;
        node_ref.set_value_pointer(trailer_offset as u32, value_size as u32);
        node_ref.set_key_offset(key_offset as u32);
        node_ref.set_key_size_and_height(encode_key_size_and_height(key_cap as u32, height as u8));
        node_ref.set_version(version);

        key.detach();
        let (_, key_deallocate_info) = self
          .fill_vacant_key(key_cap as u32, key_offset as u32, kf)
          .map_err(Among::Left)?;
        trailer_and_value.detach();
        let (_, value_deallocate_info) = self
          .fill_vacant_value(
            trailer_offset as u32,
            trailer_and_value.capacity() as u32,
            value_size as u32,
            value_offset,
            vf,
          )
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

    /// Allocates a `Node` and trailer
    fn allocate_node_in<'a, 'b: 'a, E>(
      &'a self,
      version: Version,
      height: u32,
      trailer: <Self::Node as Node>::Trailer,
      key_offset: u32,
      key_size: usize,
      value_size: usize,
    ) -> Result<(<Self::Node as Node>::Pointer, Deallocator), Either<E, Error>> {
      let key_size = key_size as u32;
      let value_size = value_size as u32;

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
        node_ref.set_value_pointer(trailer_offset as u32, value_size);
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

        Ok((
          NodePointer::new(node_offset as u32, NonNull::new_unchecked(node_ptr as _)),
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
      key_size: usize,
      kf: impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>,
      value_size: usize,
    ) -> Result<(<Self::Node as Node>::Pointer, Deallocator), Either<E, Error>> {
      let key_size = key_size as u32;
      let value_size = value_size as u32;

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
        node_ref.set_value_pointer(trailer_offset as u32, value_size);
        node_ref.set_key_offset(key_offset as u32);
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

        Ok((
          NodePointer::new(node_offset as u32, NonNull::new_unchecked(node_ptr as _)),
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

        let mut trailer_and_value = self
          .alloc_aligned_bytes::<<Self::Node as Node>::Trailer>(value_size)
          .map_err(|e| Either::Right(e.into()))?;
        let trailer_offset = trailer_and_value.offset();
        let trailer_ptr = trailer_and_value
          .as_mut_ptr()
          .cast::<<Self::Node as Node>::Trailer>();
        trailer_ptr.write(trailer);
        let value_offset =
          (trailer_offset + mem::size_of::<<Self::Node as Node>::Trailer>()) as u32;

        // Safety: the node is well aligned
        let node_ref = &mut *node_ptr;
        node_ref.set_value_pointer(trailer_offset as u32, value_size);
        node_ref.set_key_offset(key_offset);
        node_ref.set_key_size_and_height(encode_key_size_and_height(key_size as u32, height as u8));
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
      // Safety: node, links and trailer do not need to be dropped, and they are recoverable.
      unsafe {
        let mut node = self.alloc_aligned_bytes::<Self::Node>(
          ((max_height as usize) * mem::size_of::<<Self::Node as Node>::Link>()) as u32,
        )?;

        // Safety: node and trailer do not need to be dropped.
        node.detach();
        let node_offset = node.offset();

        let trailer_offset = if mem::size_of::<<Self::Node as Node>::Trailer>() != 0 {
          let mut trailer = self.alloc::<<Self::Node as Node>::Trailer>()?;
          trailer.detach();
          trailer.offset()
        } else {
          self.allocated()
        };

        let node_ptr = node.as_mut_ptr().cast::<Self::Node>();
        let full_node = <Self::Node as Node>::full(trailer_offset as u32, max_height);
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
      trailer: <Self::Node as Node>::Trailer,
      value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    ) -> Result<(), Either<E, Error>> {
      let (value_size, f) = value_builder.into_components();
      let value_size = value_size as u32;
      let mut bytes = self
        .alloc_aligned_bytes::<<Self::Node as Node>::Trailer>(value_size)
        .map_err(|e| Either::Right(e.into()))?;
      let trailer_ptr = bytes.as_mut_ptr().cast::<<Self::Node as Node>::Trailer>();
      let trailer_offset = bytes.offset();
      let value_offset = trailer_offset + mem::size_of::<<Self::Node as Node>::Trailer>();

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
        trailer_ptr.write(trailer);
      }

      if discard != 0 {
        self.increase_discarded(discard as u32);
      }

      let (_, old_len) = node.value_pointer().swap(trailer_offset as u32, value_size);
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

  type Trailer = <N as Node>::Trailer;

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
