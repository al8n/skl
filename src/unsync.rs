pub use rarena_allocator::unsync::Arena;
use rarena_allocator::Allocator as _;

use core::{
  cell::UnsafeCell,
  ops::{Bound, RangeBounds},
};

use super::{
  allocator::{Link as BaseLink, *},
  common::*,
  *,
};
use crate::VacantBuffer;

use either::Either;

/// Versioned header of the skipmap.
#[derive(Debug)]
#[repr(C)]
pub struct VersionedMeta {
  /// The maximum MVCC version of the skiplist.
  max_version: UnsafeCell<u64>,
  /// The minimum MVCC version of the skiplist.
  min_version: UnsafeCell<u64>,
  len: UnsafeCell<u32>,
  magic_version: u16,
  /// Current height. 1 <= height <= 31.
  height: UnsafeCell<u8>,
  reserved_byte: u8,
}

impl Header for VersionedMeta {
  #[inline]
  fn new(version: u16) -> Self {
    Self {
      max_version: UnsafeCell::new(0),
      min_version: UnsafeCell::new(0),
      magic_version: version,
      height: UnsafeCell::new(1),
      len: UnsafeCell::new(0),
      reserved_byte: 0,
    }
  }

  #[inline]
  fn magic_version(&self) -> u16 {
    self.magic_version
  }

  #[inline]
  fn max_version(&self) -> u64 {
    unsafe { *self.max_version.get() }
  }

  #[inline]
  fn min_version(&self) -> u64 {
    unsafe { *self.min_version.get() }
  }

  #[inline]
  fn height(&self) -> u8 {
    unsafe { *self.height.get() }
  }

  #[inline]
  fn len(&self) -> u32 {
    unsafe { *self.len.get() }
  }

  #[inline]
  fn increase_len(&self) {
    unsafe {
      *self.len.get() += 1;
    }
  }

  fn update_max_version(&self, version: Version) {
    unsafe {
      let current = *self.max_version.get();
      if version > current {
        *self.max_version.get() = version;
      }
    }
  }

  fn update_min_version(&self, version: Version) {
    unsafe {
      let current = *self.min_version.get();
      if version < current {
        *self.min_version.get() = version;
      }
    }
  }

  #[inline]
  fn compare_exchange_height_weak(
    &self,
    current: u8,
    new: u8,
    _: Ordering,
    _: Ordering,
  ) -> Result<u8, u8> {
    unsafe {
      let height = self.height.get();
      assert_eq!(
        current, *height,
        "current height is not equal to the actual height in unsync version `VersionedMeta`"
      );
      *height = new;
      Ok(current)
    }
  }
}

/// Header of the skipmap.
#[derive(Debug)]
#[repr(C)]
pub struct Meta {
  len: UnsafeCell<u32>,
  magic_version: u16,
  /// Current height. 1 <= height <= 31.
  height: UnsafeCell<u8>,
  reserved_byte: u8,
}

impl Header for Meta {
  #[inline]
  fn new(version: u16) -> Self {
    Self {
      magic_version: version,
      height: UnsafeCell::new(1),
      len: UnsafeCell::new(0),
      reserved_byte: 0,
    }
  }

  #[inline]
  fn magic_version(&self) -> u16 {
    self.magic_version
  }

  #[inline]
  fn max_version(&self) -> u64 {
    MIN_VERSION
  }

  #[inline]
  fn min_version(&self) -> u64 {
    MIN_VERSION
  }

  #[inline]
  fn height(&self) -> u8 {
    unsafe { *self.height.get() }
  }

  #[inline]
  fn len(&self) -> u32 {
    unsafe { *self.len.get() }
  }

  #[inline]
  fn increase_len(&self) {
    unsafe {
      *self.len.get() += 1;
    }
  }

  fn update_max_version(&self, _: Version) {}

  fn update_min_version(&self, _: Version) {}

  #[inline]
  fn compare_exchange_height_weak(
    &self,
    current: u8,
    new: u8,
    _: Ordering,
    _: Ordering,
  ) -> Result<u8, u8> {
    unsafe {
      let height = self.height.get();
      assert_eq!(
        current, *height,
        "current height is not equal to the actual height in unsync version `Meta`"
      );
      *height = new;
      Ok(current)
    }
  }
}

/// Atomic value pointer.
#[repr(C, align(8))]
pub struct UnsyncValuePointer(UnsafeCell<u64>);

impl core::fmt::Debug for UnsyncValuePointer {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    let (offset, len) = decode_value_pointer(unsafe { *self.0.get() });
    f.debug_struct("UnsyncValuePointer")
      .field("offset", &offset)
      .field("len", &len)
      .finish()
  }
}

impl UnsyncValuePointer {
  #[inline]
  fn new(offset: u32, len: u32) -> Self {
    Self(UnsafeCell::new(encode_value_pointer(offset, len)))
  }

  #[inline]
  fn compare_remove(&self, _: Ordering, _: Ordering) -> Result<(u32, u32), (u32, u32)> {
    unsafe {
      let ptr = self.0.get();
      let old = *ptr;

      let (offset, size) = decode_value_pointer(old);
      *ptr = encode_value_pointer(offset, REMOVE);

      Ok((offset, size))
    }
  }
}

impl ValuePointer for UnsyncValuePointer {
  const REMOVE: u32 = REMOVE;

  #[inline]
  fn load(&self) -> (u32, u32) {
    decode_value_pointer(unsafe { *self.0.get() })
  }

  #[inline]
  fn swap(&self, offset: u32, len: u32) -> (u32, u32) {
    let new = encode_value_pointer(offset, len);
    unsafe {
      let old = *self.0.get();
      *self.0.get() = new;
      decode_value_pointer(old)
    }
  }
}

/// Link to the previous and next node.
#[derive(Debug)]
#[repr(C)]
pub struct Link {
  next_offset: UnsafeCell<u32>,
  prev_offset: UnsafeCell<u32>,
}

impl BaseLink for Link {
  #[inline]
  fn new(next_offset: u32, prev_offset: u32) -> Self {
    Self {
      next_offset: UnsafeCell::new(next_offset),
      prev_offset: UnsafeCell::new(prev_offset),
    }
  }

  #[inline]
  fn store_next_offset(&self, offset: u32, _: Ordering) {
    unsafe {
      *self.next_offset.get() = offset;
    }
  }

  #[inline]
  fn store_prev_offset(&self, offset: u32, _: Ordering) {
    unsafe {
      *self.prev_offset.get() = offset;
    }
  }
}

macro_rules! node_pointer {
  ($node: ident $(<$t:ident>)?) => {
    #[doc(hidden)]
    #[derive(Debug)]
    pub struct NodePointer $(<$t>)? {
      offset: u32,
      _m: core::marker::PhantomData<$node $(<$t>)?>,
    }

    impl $(<$t>)?  Clone for NodePointer $(<$t>)? {
      fn clone(&self) -> Self {
        *self
      }
    }

    impl $(<$t>)? Copy for NodePointer $(<$t>)? {}

    impl $(<$t: $crate::Trailer>)? $crate::allocator::NodePointer for NodePointer $(<$t>)? {
      const NULL: Self = Self {
        offset: 0,
        _m: core::marker::PhantomData,
      };

      type Node = $node $(<$t>)?;

      #[inline]
      fn is_null(&self) -> bool {
        self.offset == 0
      }

      fn offset(&self) -> u32 {
        self.offset
      }

      /// ## Safety
      ///
      /// - The caller must ensure that the node is allocated by the arena.
      /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
      unsafe fn next_offset<A: $crate::allocator::Allocator>(&self, arena: &A, idx: usize) -> u32 {
        unsafe { *self.tower(arena, idx).next_offset.get() }
      }

      /// ## Safety
      ///
      /// - The caller must ensure that the node is allocated by the arena.
      /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
      unsafe fn prev_offset<A: $crate::allocator::Allocator>(&self, arena: &A, idx: usize) -> u32 {
        unsafe { *self.tower(arena, idx).prev_offset.get() }
      }

      /// ## Safety
      ///
      /// - The caller must ensure that the node is allocated by the arena.
      /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
      unsafe fn cas_prev_offset<A: $crate::allocator::Allocator>(
        &self,
        arena: &A,
        idx: usize,
        current: u32,
        new: u32,
        _: Ordering,
        _: Ordering,
      ) -> Result<u32, u32> {
        unsafe {
          let tower = self.tower(arena, idx);
          let ptr = tower.prev_offset.get();

          let old = *ptr;

          assert_eq!(old, current, "current prev_offset is not equal to the actual prev_offset in unsync version `NodePointer`, it seems that you are using unsync version in concurrent environment");

          *ptr = new;
          Ok(old)
        }
      }

      /// ## Safety
      ///
      /// - The caller must ensure that the node is allocated by the arena.
      /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
      unsafe fn cas_next_offset<A: $crate::allocator::Allocator>(
        &self,
        arena: &A,
        idx: usize,
        current: u32,
        new: u32,
        _: Ordering,
        _: Ordering,
      ) -> Result<u32, u32> {
        unsafe {
          let tower = self.tower(arena, idx);
          let ptr = tower.next_offset.get();

          let old = *ptr;

          assert_eq!(old, current, "current next_offset is not equal to the actual next_offset in unsync version `NodePointer`, it seems that you are using unsync version in concurrent environment");

          *ptr = new;
          Ok(old)
        }
      }

      #[inline]
      fn new(offset: u32) -> Self {
        Self {
          offset,
          _m: core::marker::PhantomData,
        }
      }

      /// ## Safety
      /// - the pointer must be valid
      #[inline]
      unsafe fn as_ref<A: $crate::allocator::Sealed>(&self, arena: &A) -> &Self::Node {
        &*(arena.get_pointer(self.offset as usize) as *const Self::Node)
      }

      /// ## Safety
      /// - the pointer must be valid
      #[inline]
      unsafe fn as_mut<A: $crate::allocator::Sealed>(&self, arena: &A) -> &mut Self::Node {
        &mut *(arena.get_pointer_mut(self.offset as usize) as *mut Self::Node)
      }
    }
  };
}

/// A lock free ARENA based skiplist. See [`SkipList`](base::SkipList) for more information.
pub mod full;

/// A skipmap implementation with version support. See [`SkipMap`](versioned::SkipMap) for more information.
pub mod versioned;

/// A skipmap implementation with trailer support. See [`SkipMap`](trailed::SkipMap) for more information.
pub mod trailed;

/// A skipmap implementation without trailer and version support. See [`SkipMap`](map::SkipMap) for more information.
pub mod map;

#[cfg(test)]
mod tests;
