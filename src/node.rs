use core::{mem, ptr};

use bytes::Bytes;

use crate::{
  sync::{AtomicU32, Ordering},
  NODE_ALIGNMENT_FACTOR,
};

use super::{
  arena::{Arena, ArenaError},
  MAX_HEIGHT,
};

#[derive(Debug)]
#[repr(C)]
pub(super) struct Link {
  pub(super) next_offset: AtomicU32,
  pub(super) prev_offset: AtomicU32,
}

impl Link {
  #[inline]
  pub(super) const fn new(next_offset: u32, prev_offset: u32) -> Self {
    Self {
      next_offset: AtomicU32::new(next_offset),
      prev_offset: AtomicU32::new(prev_offset),
    }
  }
}

pub(super) struct NodePtr {
  pub(super) ptr: *const Node,
  pub(super) offset: u32,
}

impl core::fmt::Debug for NodePtr {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("NodePtr")
      .field("ptr", &self.ptr)
      .field("offset", &self.offset)
      .finish()
  }
}

impl Clone for NodePtr {
  fn clone(&self) -> Self {
    *self
  }
}

impl Copy for NodePtr {}

impl NodePtr {
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
  pub(super) const unsafe fn as_ptr(&self) -> &Node {
    &*self.ptr.cast()
  }

  #[inline]
  pub(super) unsafe fn tower(&self, arena: &Arena, idx: usize) -> &Link {
    let tower_ptr_offset =
      self.offset as usize + mem::size_of::<Node>() + idx * mem::size_of::<Link>();
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
    let tower_ptr_offset =
      self.offset as usize + mem::size_of::<Node>() + idx * mem::size_of::<Link>();
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
pub(super) struct Node {
  pub(super) version: u64,

  // A byte slice is 24 bytes. We are trying to save space here.

  // Immutable. No need to lock to access key.
  pub(super) key_offset: u32,
  // Immutable. No need to lock to access key.
  pub(super) key_size: u16,
  pub(super) height: u16,

  // Immutable. No need to lock to access value.
  pub(super) value_size: u32,
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

impl Node {
  pub(super) const SIZE: usize = core::mem::size_of::<Self>();

  pub(super) const MAX_NODE_SIZE: u64 =
    (Self::SIZE + MAX_HEIGHT * core::mem::size_of::<Link>()) as u64;

  pub(super) fn new_node_ptr(
    arena: &Arena,
    height: u32,
    key: &[u8],
    version: u64,
    value: &[u8],
  ) -> Result<NodePtr, ArenaError> {
    if height < 1 || height > MAX_HEIGHT as u32 {
      panic!("height cannot be less than one or greater than the max height");
    }

    let key_size = key.len();
    if key_size as u64 > u32::MAX as u64 {
      panic!("key is too large");
    }

    let value_size = value.len();
    if value_size as u64 > u32::MAX as u64 {
      panic!("value is too large");
    }

    if (value_size as u64) + (key_size as u64) + Node::MAX_NODE_SIZE > u32::MAX as u64 {
      panic!("combined key and value size is too large");
    }

    let align = mem::align_of::<Bytes>()
      .max(mem::align_of::<Bytes>())
      .max(NODE_ALIGNMENT_FACTOR);

    // Compute the amount of the tower that will never be used, since the height
    // is less than maxHeight.
    let unused_size = (MAX_HEIGHT as u32 - height) * (mem::size_of::<Link>() as u32);
    let node_size = (Self::MAX_NODE_SIZE as u32) - unused_size;

    let (node_offset, alloc_size) = arena.alloc(
      node_size + key_size as u32 + value_size as u32,
      align as u32,
      unused_size,
    )?;

    unsafe {
      // Safety: we have check the offset is valid
      let ptr = arena.get_pointer_mut(node_offset as usize);
      // Safety: the node is well aligned
      let node = &mut *(ptr as *mut Node);
      node.version = version;
      node.key_offset = node_offset + node_size;
      node.key_size = key_size as u16;
      node.height = height as u16;
      node.value_size = value_size as u32;
      node.alloc_size = alloc_size;
      node.get_key_mut(arena).copy_from_slice(key);
      node.get_value_mut(arena).copy_from_slice(value);
      Ok(NodePtr::new(ptr, node_offset))
    }
  }

  pub(super) fn new_empty_node_ptr(arena: &Arena) -> Result<NodePtr, ArenaError> {
    // Compute the amount of the tower that will never be used, since the height
    // is less than maxHeight.
    let align = mem::align_of::<Bytes>()
      .max(mem::align_of::<Bytes>())
      .max(NODE_ALIGNMENT_FACTOR);
    let (node_offset, alloc_size) = arena.alloc(Node::MAX_NODE_SIZE as u32, align as u32, 0)?;

    // Safety: we have check the offset is valid
    unsafe {
      let ptr = arena.get_pointer_mut(node_offset as usize);
      // Safety: the node is well aligned
      let node = &mut *(ptr as *mut Node);
      node.version = 0;
      node.key_offset = 0;
      node.key_size = 0;
      node.value_size = 0;
      node.height = MAX_HEIGHT as u16;
      node.alloc_size = alloc_size;
      Ok(NodePtr::new(ptr, node_offset))
    }
  }
}

impl Node {
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
  pub(super) unsafe fn get_value<'a, 'b: 'a>(&'a self, arena: &'b Arena) -> &'b [u8] {
    arena.get_bytes(
      self.key_offset as usize + self.key_size as usize,
      self.value_size as usize,
    )
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[allow(clippy::mut_from_ref)]
  pub(super) unsafe fn get_value_mut<'a, 'b: 'a>(&'a mut self, arena: &'b Arena) -> &'b mut [u8] {
    arena.get_bytes_mut(
      self.key_offset as usize + self.key_size as usize,
      self.value_size as usize,
    )
  }
}
