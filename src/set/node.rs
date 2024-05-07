use core::{mem, ptr};

use crate::{
  sync::{Link, Ordering},
  Trailer,
};

use super::{
  super::arena::{Arena, ArenaError},
  Error, MAX_HEIGHT,
};

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

  // Immutable. No need to lock to access key.
  pub(super) key_offset: u32,
  // Immutable. No need to lock to access key.
  pub(super) key_size: u32,
  pub(super) height: u16,

  // Immutable. No need to lock to access
  pub(super) alloc_size: u32,
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
    let alignment = if alignment < mem::size_of::<u32>() {
      mem::size_of::<u32>()
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
    let (node_offset, alloc_size) = arena.alloc(Self::max_node_size(), Self::alignment(), 0)?;

    // Safety: we have check the offset is valid
    unsafe {
      let ptr = arena.get_pointer_mut(node_offset as usize);
      // Safety: the node is well aligned
      let node = &mut *(ptr as *mut Node<T>);
      node.key_offset = 0;
      node.key_size = 0;
      node.height = MAX_HEIGHT as u16;
      node.alloc_size = alloc_size;
      Ok(NodePtr::new(ptr, node_offset))
    }
  }
}
impl<T: Trailer> Node<T> {
  pub(super) fn new_node_ptr(
    arena: &Arena,
    height: u32,
    key: &[u8],
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

    let (node_offset, alloc_size) =
      arena.alloc(node_size + key_size as u32, Self::alignment(), unused_size)?;

    unsafe {
      // Safety: we have check the offset is valid
      let ptr = arena.get_pointer_mut(node_offset as usize);
      // Safety: the node is well aligned
      let node = &mut *(ptr as *mut Node<T>);
      node.trailer = trailer;
      node.key_offset = node_offset + node_size;
      node.key_size = key_size as u32;
      node.height = height as u16;
      node.alloc_size = alloc_size;
      node.get_key_mut(arena).copy_from_slice(key);
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
}

#[cfg(test)]
#[test]
fn test_clone() {
  let node_ptr = NodePtr::<u8>::NULL;
  #[allow(clippy::clone_on_copy)]
  let _ = node_ptr.clone();
}
