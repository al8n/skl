use core::{mem, ptr};

use crate::sync::{AtomicU64, Link};

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
    self.tower(arena, idx).next_offset.load(Ordering::Acquire)
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
  pub(super) unsafe fn prev_offset(&self, arena: &Arena, idx: usize) -> u32 {
    self.tower(arena, idx).prev_offset.load(Ordering::Acquire)
  }
}

#[derive(Debug)]
#[repr(C)]
pub(super) struct Node<T> {
  pub(super) trailer: T,

  // A byte slice is 24 bytes. We are trying to save space here.
  /// Multiple parts of the value are encoded as a single uint64 so that it
  /// can be atomically loaded and stored:
  ///   value offset: u32 (bits 0-31)
  ///   value size  : u32 (bits 32-63)
  pub(super) value: AtomicU64,
  // Immutable. No need to lock to access key.
  pub(super) key_offset: u32,
  // Immutable. No need to lock to access key.
  pub(super) key_size: u16,
  pub(super) height: u16,
  // // Immutable. No need to lock to access value.
  // pub(super) value_size: u32,
  // // Immutable. No need to lock to access
  // pub(super) alloc_size: u32,
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

  pub(super) const MAX_NODE_SIZE: u64 = (Self::SIZE + MAX_HEIGHT * Link::SIZE) as u64;

  #[inline]
  pub(super) const fn min_cap() -> usize {
    (Node::<T>::MAX_NODE_SIZE * 2) as usize
  }

  #[inline]
  pub(super) const fn alignment() -> u32 {
    let alignment = mem::align_of::<T>();
    let alignment = if alignment < mem::align_of::<u64>() {
      mem::align_of::<u64>()
    } else {
      alignment
    };
    alignment as u32
  }

  #[inline]
  const fn max_node_size() -> u32 {
    Node::<T>::MAX_NODE_SIZE as u32
  }

  pub(super) fn new_empty_node_ptr(arena: &Arena) -> Result<NodePtr<T>, ArenaError> {
    // Compute the amount of the tower that will never be used, since the height
    // is less than maxHeight.
    let node_offset = arena.alloc(Self::max_node_size(), Self::alignment(), 0)?;

    // Safety: we have check the offset is valid
    unsafe {
      let ptr = arena.get_pointer_mut(node_offset as usize);
      // Safety: the node is well aligned
      let node = &mut *(ptr as *mut Node<T>);
      node.value = AtomicU64::new(encode_value(node_offset + Self::MAX_NODE_SIZE as u32, 0));
      node.key_offset = 0;
      node.key_size = 0;
      node.height = MAX_HEIGHT as u16;
      Ok(NodePtr::new(ptr, node_offset))
    }
  }

  #[inline]
  pub(super) fn set_value<'a, E>(
    &self,
    arena: &'a Arena,
    value_size: u32,
    f: impl FnOnce(OccupiedValue<'a>) -> Result<(), E>,
  ) -> Result<(), Either<E, Error>> {
    let offset = Self::new_value(arena, value_size, f)?;
    self
      .value
      .store(encode_value(offset, value_size), Ordering::Release);
    Ok(())
  }

  fn new_value<'a, E>(
    arena: &'a Arena,
    value_size: u32,
    f: impl FnOnce(OccupiedValue<'a>) -> Result<(), E>,
  ) -> Result<u32, Either<E, Error>> {
    if value_size as u64 > u32::MAX as u64 {
      return Err(Either::Right(Error::ValueTooLarge(value_size as u64)));
    }

    let value_offset = arena
      .alloc_value(value_size)
      .map_err(|e: ArenaError| Either::Right(e.into()))?;

    // Safety: we have check the offset is valid
    unsafe {
      let ptr = arena.get_pointer_mut(value_offset as usize);
      let val = core::slice::from_raw_parts_mut(ptr, value_size as usize);
      f(OccupiedValue::new(value_size as usize, val)).map_err(Either::Left)?;
      Ok(value_offset)
    }
  }
}

impl<T: Trailer> Node<T> {
  pub(super) fn new_node_ptr<'a, 'b: 'a, E>(
    arena: &'a Arena,
    height: u32,
    key: &'b [u8],
    trailer: T,
    value_size: u32,
    f: impl FnOnce(OccupiedValue<'a>) -> Result<(), E>,
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

    let node_offset = arena
      .alloc(
        node_size + key_size as u32 + value_size,
        Self::alignment(),
        unused_size,
      )
      .map_err(|e| Either::Right(e.into()))?;

    unsafe {
      // Safety: we have check the offset is valid
      let ptr = arena.get_pointer_mut(node_offset as usize);
      // Safety: the node is well aligned
      let node = &mut *(ptr as *mut Node<T>);
      node.value = AtomicU64::new(encode_value(
        node_offset + node_size + key_size as u32,
        value_size,
      ));
      node.trailer = trailer;
      node.key_offset = node_offset + node_size;
      node.key_size = key_size as u16;
      node.height = height as u16;
      node.get_key_mut(arena).copy_from_slice(key);
      f(OccupiedValue::new(
        value_size as usize,
        node.get_value_mut(arena),
      ))
      .map_err(Either::Left)?;
      Ok(NodePtr::new(ptr, node_offset))
    }
  }
}

impl<T> Node<T> {
  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  pub(super) unsafe fn get_key<'a, 'b: 'a>(&'a self, arena: &'b Arena) -> &'b [u8] {
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
  pub(super) unsafe fn get_value<'a, 'b: 'a>(&'a self, arena: &'b Arena) -> Option<&'b [u8]> {
    let (offset, val_size) = decode_value(self.value.load(Ordering::Acquire));
    if offset == 0 && val_size == 0 {
      return None;
    }

    Some(arena.get_bytes(offset as usize, val_size as usize))
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[allow(clippy::mut_from_ref)]
  pub(super) unsafe fn get_value_mut<'a, 'b: 'a>(&'a mut self, arena: &'b Arena) -> &'b mut [u8] {
    let (offset, val_size) = decode_value(self.value.load(Ordering::Acquire));
    arena.get_bytes_mut(offset as usize, val_size as usize)
  }
}

#[inline]
const fn encode_value(offset: u32, val_size: u32) -> u64 {
  (val_size as u64) << 32 | offset as u64
}

#[inline]
const fn decode_value(value: u64) -> (u32, u32) {
  let offset = value as u32;
  let val_size = (value >> 32) as u32;
  (offset, val_size)
}

#[cfg(test)]
#[test]
fn test_clone() {
  let node_ptr = NodePtr::<u8>::NULL;
  #[allow(clippy::clone_on_copy)]
  let _ = node_ptr.clone();
}
