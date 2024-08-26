use rarena_allocator::{sync::Arena, Allocator as _};

use core::{
  ops::{Bound, RangeBounds},
  ptr,
};

use crate::VacantBuffer;

use super::{common::*, *};

use super::base::{Allocator as BaseAllocator, Link as BaseLink, Node as BaseNode, *};

use either::Either;

/// Header of the skiplist.
#[derive(Debug)]
#[repr(C)]
pub struct Meta {
  /// The maximum MVCC version of the skiplist. CAS.
  max_version: AtomicU64,
  /// The minimum MVCC version of the skiplist. CAS.
  min_version: AtomicU64,
  len: AtomicU32,
  magic_version: u16,
  /// Current height. 1 <= height <= 31. CAS.
  height: AtomicU8,
  reserved_byte: u8,
}

impl Header for Meta {
  #[inline]
  fn new(version: u16) -> Self {
    Self {
      max_version: AtomicU64::new(0),
      min_version: AtomicU64::new(0),
      magic_version: version,
      height: AtomicU8::new(1),
      len: AtomicU32::new(0),
      reserved_byte: 0,
    }
  }

  #[inline]
  fn magic_version(&self) -> u16 {
    self.magic_version
  }

  #[inline]
  fn max_version(&self) -> u64 {
    self.max_version.load(Ordering::Acquire)
  }

  #[inline]
  fn min_version(&self) -> u64 {
    self.min_version.load(Ordering::Acquire)
  }

  #[inline]
  fn height(&self) -> u8 {
    self.height.load(Ordering::Acquire)
  }

  #[inline]
  fn len(&self) -> u32 {
    self.len.load(Ordering::Acquire)
  }

  #[inline]
  fn increase_len(&self) {
    self.len.fetch_add(1, Ordering::Release);
  }

  fn update_max_version(&self, version: Version) {
    let mut current = self.max_version.load(Ordering::Acquire);
    loop {
      if version <= current {
        return;
      }

      match self.max_version.compare_exchange_weak(
        current,
        version,
        Ordering::SeqCst,
        Ordering::Acquire,
      ) {
        Ok(_) => break,
        Err(v) => current = v,
      }
    }
  }

  fn update_min_version(&self, version: Version) {
    let mut current = self.min_version.load(Ordering::Acquire);
    loop {
      if version >= current {
        return;
      }

      match self.min_version.compare_exchange_weak(
        current,
        version,
        Ordering::SeqCst,
        Ordering::Acquire,
      ) {
        Ok(_) => break,
        Err(v) => current = v,
      }
    }
  }

  #[inline]
  fn compare_exchange_height_weak(
    &self,
    current: u8,
    new: u8,
    success: Ordering,
    failure: Ordering,
  ) -> Result<u8, u8> {
    self
      .height
      .compare_exchange_weak(current, new, success, failure)
  }
}

/// Atomic value pointer.
#[repr(C, align(8))]
pub struct AtomicValuePointer(AtomicU64);

impl core::fmt::Debug for AtomicValuePointer {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    let (offset, len) = decode_value_pointer(self.0.load(Ordering::Relaxed));
    f.debug_struct("AtomicValuePointer")
      .field("offset", &offset)
      .field("len", &len)
      .finish()
  }
}

impl AtomicValuePointer {
  #[inline]
  fn new(offset: u32, len: u32) -> Self {
    Self(AtomicU64::new(encode_value_pointer(offset, len)))
  }

  #[inline]
  fn compare_remove(&self, success: Ordering, failure: Ordering) -> Result<(u32, u32), (u32, u32)> {
    let old = self.0.load(Ordering::Acquire);
    let (offset, _) = decode_value_pointer(old);
    let new = encode_value_pointer(offset, REMOVE);
    self
      .0
      .compare_exchange(old, new, success, failure)
      .map(decode_value_pointer)
      .map_err(decode_value_pointer)
  }
}

impl ValuePointer for AtomicValuePointer {
  const REMOVE: u32 = REMOVE;

  #[inline]
  fn load(&self) -> (u32, u32) {
    decode_value_pointer(AtomicU64::load(&self.0, Ordering::Acquire))
  }

  #[inline]
  fn swap(&self, offset: u32, len: u32) -> (u32, u32) {
    decode_value_pointer(
      self
        .0
        .swap(encode_value_pointer(offset, len), Ordering::AcqRel),
    )
  }
}

/// Link to the previous and next node.
#[derive(Debug)]
#[repr(C)]
pub struct Link {
  next_offset: AtomicU32,
  prev_offset: AtomicU32,
}

impl BaseLink for Link {
  #[inline]
  fn new(next_offset: u32, prev_offset: u32) -> Self {
    Self {
      next_offset: AtomicU32::new(next_offset),
      prev_offset: AtomicU32::new(prev_offset),
    }
  }

  #[inline]
  fn store_next_offset(&self, offset: u32, ordering: Ordering) {
    self.next_offset.store(offset, ordering);
  }

  #[inline]
  fn store_prev_offset(&self, offset: u32, ordering: Ordering) {
    self.prev_offset.store(offset, ordering);
  }
}

macro_rules! node_pointer {
  ($node: ident $(<$t:ident>)?) => {
    #[doc(hidden)]
    #[derive(Debug)]
    pub struct NodePointer $(<$t>)? {
      ptr: *mut $node $(<$t>)?,
      offset: u32,
    }

    impl $(<$t>)?  Clone for NodePointer $(<$t>)? {
      fn clone(&self) -> Self {
        *self
      }
    }

    impl $(<$t>)? Copy for NodePointer $(<$t>)? {}

    impl $(<$t: $crate::Trailer>)? $crate::base::NodePointer for NodePointer $(<$t>)? {
      const NULL: Self = Self {
        ptr: ptr::null_mut(),
        offset: 0,
      };

      type Node = $node $(<$t>)?;

      #[inline]
      fn is_null(&self) -> bool {
        self.offset == 0
      }

      fn offset(&self) -> u32 {
        self.offset
      }

      fn ptr(&self) -> *mut Self::Node {
        self.ptr
      }

      /// ## Safety
      ///
      /// - The caller must ensure that the node is allocated by the arena.
      /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
      unsafe fn next_offset<A: $crate::base::Allocator>(&self, arena: &A, idx: usize) -> u32 {
        self.tower(arena, idx).next_offset.load(Ordering::Acquire)
      }

      /// ## Safety
      ///
      /// - The caller must ensure that the node is allocated by the arena.
      /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
      unsafe fn prev_offset<A: $crate::base::Allocator>(&self, arena: &A, idx: usize) -> u32 {
        self.tower(arena, idx).prev_offset.load(Ordering::Acquire)
      }

      /// ## Safety
      ///
      /// - The caller must ensure that the node is allocated by the arena.
      /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
      unsafe fn cas_prev_offset<A: $crate::base::Allocator>(
        &self,
        arena: &A,
        idx: usize,
        current: u32,
        new: u32,
        success: Ordering,
        failure: Ordering,
      ) -> Result<u32, u32> {
        self
          .tower(arena, idx)
          .prev_offset
          .compare_exchange(current, new, success, failure)
      }

      /// ## Safety
      ///
      /// - The caller must ensure that the node is allocated by the arena.
      /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
      unsafe fn cas_next_offset<A: $crate::base::Allocator>(
        &self,
        arena: &A,
        idx: usize,
        current: u32,
        new: u32,
        success: Ordering,
        failure: Ordering,
      ) -> Result<u32, u32> {
        self
          .tower(arena, idx)
          .next_offset
          .compare_exchange(current, new, success, failure)
      }

      #[inline]
      fn new(ptr: *mut u8, offset: u32) -> Self {
        Self {
          ptr: ptr.cast(),
          offset,
        }
      }

      /// ## Safety
      /// - the pointer must be valid
      #[inline]
      unsafe fn as_ref(&self) -> &Self::Node {
        &*self.ptr.cast()
      }

      /// ## Safety
      /// - the pointer must be valid
      #[inline]
      unsafe fn as_mut(&self) -> &mut Self::Node {
        &mut *self.ptr.cast()
      }
    }
  };
}

/// A lock free ARENA based skiplist. See [`SkipList`](base::SkipList) for more information.
pub mod base;

/// A skipmap implementation with version support. See [`SkipMap`](versioned::SkipMap) for more information.
pub mod versioned;

/// A skipmap implementation with trailer support. See [`SkipMap`](trailed::SkipMap) for more information.
pub mod trailed;

/// A skipmap implementation without trailer and version support. See [`SkipMap`](map::SkipMap) for more information.
pub mod map;
