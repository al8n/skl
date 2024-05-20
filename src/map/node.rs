use core::{marker::PhantomData, mem, ptr};

use crate::{arena::AllocMeta, sync::*, Pointer};

use super::{super::arena::ArenaError, *};

#[derive(Debug)]
pub(crate) struct NodePtr<T> {
  pub(super) ptr: *const Node<T>,
  pub(super) offset: u32,
}

impl<T> Clone for NodePtr<T> {
  fn clone(&self) -> Self {
    *self
  }
}

impl<T> Copy for NodePtr<T> {}

impl<T> NodePtr<T> {
  pub(super) const NULL: Self = Self {
    ptr: ptr::null(),
    offset: 0,
  };

  #[inline]
  pub(super) const fn new(ptr: *const u8, offset: u32) -> Self {
    Self {
      ptr: ptr.cast(),
      offset,
    }
  }

  #[inline]
  pub(super) fn is_null(&self) -> bool {
    self.ptr.is_null()
  }

  /// ## Safety
  /// - the pointer must be valid
  #[inline]
  pub(super) const unsafe fn as_ptr(&self) -> &Node<T> {
    &*self.ptr.cast()
  }

  #[inline]
  pub(super) unsafe fn tower(&self, arena: &Arena, idx: usize) -> &Link {
    let tower_ptr_offset = self.offset as usize + Node::<T>::SIZE + idx * Link::SIZE;
    let tower_ptr = arena.get_pointer(tower_ptr_offset);
    &*tower_ptr.cast()
  }

  #[inline]
  pub(super) unsafe fn write_tower(
    &self,
    arena: &Arena,
    idx: usize,
    prev_offset: u32,
    next_offset: u32,
  ) {
    let tower_ptr_offset = self.offset as usize + Node::<T>::SIZE + idx * Link::SIZE;
    let tower_ptr: *mut Link = arena.get_pointer_mut(tower_ptr_offset).cast();
    *tower_ptr = Link::new(next_offset, prev_offset);
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
  pub(super) unsafe fn next_offset(&self, arena: &Arena, idx: usize) -> u32 {
    #[cfg(not(feature = "unaligned"))]
    self.tower(arena, idx).next_offset.load(Ordering::Acquire)
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
  pub(super) unsafe fn prev_offset(&self, arena: &Arena, idx: usize) -> u32 {
    #[cfg(not(feature = "unaligned"))]
    self.tower(arena, idx).prev_offset.load(Ordering::Acquire)
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
  pub(super) unsafe fn cas_prev_offset(
    &self,
    arena: &Arena,
    idx: usize,
    current: u32,
    new: u32,
    success: Ordering,
    failure: Ordering,
  ) -> Result<u32, u32> {
    #[cfg(not(feature = "unaligned"))]
    self
      .tower(arena, idx)
      .prev_offset
      .compare_exchange(current, new, success, failure)
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
  pub(super) unsafe fn cas_next_offset_weak(
    &self,
    arena: &Arena,
    idx: usize,
    current: u32,
    new: u32,
    success: Ordering,
    failure: Ordering,
  ) -> Result<u32, u32> {
    #[cfg(not(feature = "unaligned"))]
    self
      .tower(arena, idx)
      .next_offset
      .compare_exchange_weak(current, new, success, failure)
  }
}

#[derive(Debug)]
#[cfg_attr(all(feature = "atomic", feature = "std"), repr(C, align(4)))]
#[cfg_attr(not(all(feature = "atomic", feature = "std")), repr(C, align(8)))]
pub(super) struct Node<T> {
  // A byte slice is 24 bytes. We are trying to save space here.
  /// Multiple parts of the value are encoded as a single uint64 so that it
  /// can be atomically loaded and stored:
  ///   value offset: u32 (bits 0-31)
  ///   value size  : u32 (bits 32-63)
  pub(super) value: Pointer,
  // Immutable. No need to lock to access key.
  pub(super) key_offset: u32,
  // Immutable. No need to lock to access key.
  pub(super) key_size: u16,
  pub(super) height: u16,
  trailer: PhantomData<T>,
  // ** DO NOT REMOVE BELOW COMMENT**
  // The below field will be attached after the node, have to comment out
  // this field, because each node will not use the full height, the code will
  // not allocate the full size of the tower.
  //
  // Most nodes do not need to use the full height of the tower, since the
  // probability of each successive level decreases exponentially. Because
  // these elements are never accessed, they do not need to be allocated.
  // Therefore, when a node is allocated in the arena, its memory footprint
  // is deliberately truncated to not include unneeded tower elements.
  //
  // All accesses to elements should use CAS operations, with no need to lock.
  // pub(super) tower: [Link; Self::MAX_HEIGHT],
}

impl<T> Node<T> {
  pub(super) const SIZE: usize = mem::size_of::<Self>();
  pub(super) const ALIGN: u32 = mem::align_of::<Self>() as u32;

  pub(super) const MAX_NODE_SIZE: u64 = (Self::SIZE + MAX_HEIGHT * Link::SIZE) as u64;

  #[inline]
  pub(super) const fn min_cap() -> usize {
    (Node::<T>::MAX_NODE_SIZE * 2) as usize
  }

  #[inline]
  const fn max_node_size() -> u32 {
    Node::<T>::MAX_NODE_SIZE as u32
  }

  #[inline]
  pub(super) fn size(&self) -> u32 {
    let pad = (Self::SIZE + self.height as usize * Link::SIZE + self.key_size as usize) as u32
      + Self::ALIGN
      - 1;
    let trailer_pad = (mem::size_of::<T>() + mem::align_of::<T>() - 1) as u32;
    let (_, value_size) = self.value.load(Ordering::Acquire);
    if value_size != u32::MAX {
      pad + trailer_pad + value_size
    } else {
      pad + trailer_pad
    }
  }

  pub(super) fn new_empty_node_ptr(arena: &Arena) -> Result<NodePtr<T>, ArenaError> {
    // Compute the amount of the tower that will never be used, since the height
    // is less than maxHeight.
    let AllocMeta {
      node_offset,
      value_offset,
      allocated: _,
    } = arena.alloc::<T>(Self::max_node_size(), 0, Self::ALIGN, 0)?;

    // Safety: we have check the offset is valid
    unsafe {
      let ptr = arena.get_pointer_mut(node_offset as usize);
      // Safety: the node is well aligned
      let node = &mut *(ptr as *mut Node<T>);
      let trailer_ptr = arena.get_pointer_mut(value_offset as usize);
      #[cfg(not(feature = "unaligned"))]
      ptr::write_bytes(trailer_ptr as *mut T, 0, 1);

      node.value = Pointer::new(value_offset, 0);
      node.key_offset = 0;
      node.key_size = 0;
      node.height = MAX_HEIGHT as u16;

      #[cfg(not(feature = "unaligned"))]
      ptr::write_bytes(ptr.add(mem::size_of::<Node<T>>()), 0, MAX_HEIGHT);

      Ok(NodePtr::new(ptr, node_offset))
    }
  }

  #[inline]
  pub(super) fn set_value<'a, E>(
    &self,
    arena: &'a Arena,
    trailer: T,
    value_size: u32,
    f: impl FnOnce(&mut VacantValue<'a>) -> Result<(), E>,
  ) -> Result<(), Either<E, Error>> {
    let offset = Self::new_value(arena, trailer, value_size, f)?;
    let (_, old_size) = self.value.swap(offset, value_size);

    // on success, which means that old value is removed, we need to incr the discard bytes
    // if size is u32::MAX, it means the value is already removed, we do not need to incr the discard bytes
    if old_size != u32::MAX {
      let padded = Arena::pad_value_and_trailer::<T>(old_size);

      arena.incr_discard(padded as u32);
    } else {
      let padded = Arena::pad_value_and_trailer::<T>(0);
      arena.incr_discard(padded as u32);
    }

    Ok(())
  }

  #[inline]
  pub(super) fn clear_value(
    &self,
    arena: &Arena,
    success: Ordering,
    failure: Ordering,
  ) -> Result<(u32, u32), (u32, u32)> {
    self
      .value
      .compare_remove(success, failure)
      .map(|(offset, size)| {
        // on success, which means that old value is removed, we need to incr the discard bytes
        // if size is u32::MAX, it means the value is already removed, we do not need to incr the discard bytes
        if size != u32::MAX {
          let padded = Arena::pad_value_and_trailer::<T>(size);

          arena.incr_discard(padded as u32);
        } else {
          let padded = Arena::pad_value_and_trailer::<T>(0);
          arena.incr_discard(padded as u32);
        }
        (offset, size)
      })
  }

  pub(super) fn new_value<'a, E>(
    arena: &'a Arena,
    trailer: T,
    value_size: u32,
    f: impl FnOnce(&mut VacantValue<'a>) -> Result<(), E>,
  ) -> Result<u32, Either<E, Error>> {
    if value_size as u64 > u32::MAX as u64 {
      return Err(Either::Right(Error::ValueTooLarge(value_size as u64)));
    }

    let value_offset = arena
      .alloc_value::<T>(value_size)
      .map_err(|e: ArenaError| Either::Right(e.into()))?;

    // Safety: we have check the offset is valid
    unsafe {
      let ptr = arena.get_pointer_mut(value_offset as usize);
      let trailer_ptr = ptr as *mut T;
      #[cfg(not(feature = "unaligned"))]
      ptr::write(trailer_ptr, trailer);

      let val = core::slice::from_raw_parts_mut(ptr.add(mem::size_of::<T>()), value_size as usize);
      Self::fill_vacant_value(arena, value_size, val, f).map_err(Either::Left)?;
      Ok(value_offset)
    }
  }

  #[inline]
  unsafe fn fill_vacant_value<'a, E>(
    arena: &'a Arena,
    value_size: u32,
    buf: &'a mut [u8],
    f: impl FnOnce(&mut VacantValue<'a>) -> Result<(), E>,
  ) -> Result<(), E> {
    let mut oval = VacantValue::new(value_size as usize, buf);
    f(&mut oval)?;
    let remaining = oval.remaining();
    if remaining != 0 {
      #[cfg(feature = "tracing")]
      tracing::warn!("vacant value is not fully filled, remaining {remaining} bytes");

      arena.incr_discard(remaining as u32);
    }
    Ok(())
  }
}

impl<T: Trailer> Node<T> {
  pub(super) fn new_node_ptr<'a, 'b: 'a, E>(
    arena: &'a Arena,
    height: u32,
    key: &'b [u8],
    trailer: T,
    value_size: u32,
    f: impl FnOnce(&mut VacantValue<'a>) -> Result<(), E>,
  ) -> Result<NodePtr<T>, Either<E, Error>> {
    if height < 1 || height > MAX_HEIGHT as u32 {
      panic!("height cannot be less than one or greater than the max height");
    }

    let key_size = key.len();
    if key_size as u64 > u32::MAX as u64 {
      return Err(Either::Right(Error::KeyTooLarge(key_size as u64)));
    }

    if value_size as u64 > u32::MAX as u64 {
      return Err(Either::Right(Error::ValueTooLarge(value_size as u64)));
    }

    let entry_size = (value_size as u64) + (key_size as u64) + Node::<T>::MAX_NODE_SIZE;
    if entry_size > u32::MAX as u64 {
      return Err(Either::Right(Error::EntryTooLarge(entry_size)));
    }

    // Compute the amount of the tower that will never be used, since the height
    // is less than maxHeight.
    let unused_size = (MAX_HEIGHT as u32 - height) * (Link::SIZE as u32);
    let node_size = (Self::MAX_NODE_SIZE as u32) - unused_size;

    let AllocMeta {
      node_offset,
      value_offset,
      allocated: _,
    } = arena
      .alloc::<T>(
        node_size + key_size as u32,
        value_size,
        Self::ALIGN,
        unused_size,
      )
      .map_err(|e| Either::Right(e.into()))?;

    unsafe {
      // Safety: we have check the offset is valid
      let ptr = arena.get_pointer_mut(node_offset as usize);
      // Safety: the node is well aligned
      let node = &mut *(ptr as *mut Node<T>);
      node.value = Pointer::new(value_offset, value_size);
      node.key_offset = node_offset + node_size;
      node.key_size = key_size as u16;
      node.height = height as u16;
      node.get_key_mut(arena).copy_from_slice(key);

      #[cfg(not(feature = "unaligned"))]
      ptr::write_bytes(ptr.add(mem::size_of::<Node<T>>()), 0, height as usize);

      let ptr = arena.get_pointer_mut(value_offset as usize);
      let trailer_ptr = ptr as *mut T;
      #[cfg(not(feature = "unaligned"))]
      ptr::write(trailer_ptr, trailer);

      Self::fill_vacant_value(arena, value_size, node.get_value_mut(arena), f)
        .map_err(Either::Left)?;

      Ok(NodePtr::new(ptr, node_offset))
    }
  }

  pub(super) fn new_remove_node_ptr<'a, 'b: 'a>(
    arena: &'a Arena,
    height: u32,
    key: &'b [u8],
    trailer: T,
  ) -> Result<NodePtr<T>, Error> {
    if height < 1 || height > MAX_HEIGHT as u32 {
      panic!("height cannot be less than one or greater than the max height");
    }

    let key_size = key.len();
    if key_size as u64 > u32::MAX as u64 {
      return Err(Error::KeyTooLarge(key_size as u64));
    }

    let entry_size = (key_size as u64) + Node::<T>::MAX_NODE_SIZE;
    if entry_size > u32::MAX as u64 {
      return Err(Error::EntryTooLarge(entry_size));
    }

    // Compute the amount of the tower that will never be used, since the height
    // is less than maxHeight.
    let unused_size = (MAX_HEIGHT as u32 - height) * (Link::SIZE as u32);
    let node_size = (Self::MAX_NODE_SIZE as u32) - unused_size;

    let AllocMeta {
      node_offset,
      value_offset,
      allocated,
    } = arena.alloc::<T>(node_size + key_size as u32, 0, Self::ALIGN, unused_size)?;

    unsafe {
      // Safety: we have check the offset is valid
      let ptr = arena.get_pointer_mut(node_offset as usize);
      // Safety: the node is well aligned
      let node = &mut *(ptr as *mut Node<T>);
      node.value = Pointer::remove(value_offset);
      node.key_offset = node_offset + node_size;
      node.key_size = key_size as u16;
      node.height = height as u16;
      node.get_key_mut(arena).copy_from_slice(key);
      #[cfg(not(feature = "unaligned"))]
      ptr::write_bytes(ptr.add(mem::size_of::<Node<T>>()), 0, height as usize);

      let ptr = arena.get_pointer_mut(value_offset as usize);
      let trailer_ptr = ptr as *mut T;
      #[cfg(not(feature = "unaligned"))]
      ptr::write(trailer_ptr, trailer);
      arena.incr_discard(allocated);
      Ok(NodePtr::new(ptr, node_offset))
    }
  }
}

impl<T> Node<T> {
  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  pub(super) const unsafe fn get_key<'a, 'b: 'a>(&'a self, arena: &'b Arena) -> &'b [u8] {
    arena.get_bytes(self.key_offset as usize, self.key_size as usize)
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[allow(clippy::mut_from_ref)]
  pub(super) unsafe fn get_key_mut<'a, 'b: 'a>(&'a mut self, arena: &'b Arena) -> &'b mut [u8] {
    arena.get_bytes_mut(self.key_offset as usize, self.key_size as usize)
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[inline]
  pub(super) unsafe fn get_value_mut<'a, 'b: 'a>(&'a mut self, arena: &'b Arena) -> &'b mut [u8] {
    let (offset, len) = self.value.load(Ordering::Acquire);
    arena.get_bytes_mut(offset as usize + mem::size_of::<T>(), len as usize)
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[inline]
  pub(super) unsafe fn get_value<'a, 'b: 'a>(&'a self, arena: &'b Arena) -> Option<&'b [u8]> {
    let (offset, len) = self.value.load(Ordering::Acquire);

    if len == u32::MAX {
      return None;
    }

    Some(arena.get_bytes(offset as usize + mem::size_of::<T>(), len as usize))
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[inline]
  pub(super) unsafe fn get_value_by_offset<'a, 'b: 'a>(
    &'a self,
    arena: &'b Arena,
    offset: u32,
    len: u32,
  ) -> Option<&'b [u8]> {
    if len == u32::MAX {
      return None;
    }

    Some(arena.get_bytes(offset as usize + mem::size_of::<T>(), len as usize))
  }
}

impl<T: Copy> Node<T> {
  #[inline]
  pub(super) unsafe fn get_trailer<'a, 'b: 'a>(&'a self, arena: &'b Arena) -> T {
    let (offset, _) = self.value.load(Ordering::Acquire);
    let ptr = arena.get_pointer(offset as usize);
    #[cfg(not(feature = "unaligned"))]
    ptr::read(ptr as *const T)
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[inline]
  pub(super) unsafe fn get_trailer_by_offset<'a, 'b: 'a>(
    &'a self,
    arena: &'b Arena,
    offset: u32,
  ) -> T {
    let ptr = arena.get_pointer(offset as usize);
    #[cfg(not(feature = "unaligned"))]
    ptr::read(ptr as *const T)
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[inline]
  pub(super) unsafe fn get_value_and_trailer<'a, 'b: 'a>(
    &'a self,
    arena: &'b Arena,
  ) -> (T, Option<&'b [u8]>) {
    let (offset, len) = self.value.load(Ordering::Acquire);
    let ptr = arena.get_pointer(offset as usize);
    #[cfg(not(feature = "unaligned"))]
    let trailer = ptr::read(ptr as *const T);

    if len == u32::MAX {
      return (trailer, None);
    }

    (
      trailer,
      Some(arena.get_bytes(offset as usize + mem::size_of::<T>(), len as usize)),
    )
  }
}

#[cfg(test)]
#[test]
fn test_clone() {
  let node_ptr = NodePtr::<u8>::NULL;
  #[allow(clippy::clone_on_copy)]
  let _ = node_ptr.clone();
}
