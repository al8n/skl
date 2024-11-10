pub use rarena_allocator::sync::Arena;

use core::ptr::NonNull;

use crate::internal::Flags;

use super::{
  allocator::{Link as ContainerLink, *},
  common::*,
  decode_value_pointer, encode_value_pointer, Version, MIN_VERSION, REMOVE,
};

/// Versioned header of the skiplist.
#[derive(Debug)]
#[repr(C)]
pub struct VersionedMeta {
  /// The maximum MVCC version of the skiplist. CAS.
  maximum_version: AtomicU64,
  /// The minimum MVCC version of the skiplist. CAS.
  minimum_version: AtomicU64,
  len: AtomicU32,
  magic_version: u16,
  /// Current height. 1 <= height <= 31. CAS.
  height: AtomicU8,
  flags: Flags,
}

impl crate::allocator::Meta for VersionedMeta {
  #[inline]
  fn new(version: u16) -> Self {
    Self {
      maximum_version: AtomicU64::new(0),
      minimum_version: AtomicU64::new(0),
      magic_version: version,
      height: AtomicU8::new(1),
      len: AtomicU32::new(0),
      flags: Flags::MULTIPLE_VERSION,
    }
  }

  #[inline]
  fn magic_version(&self) -> u16 {
    self.magic_version
  }

  #[inline]
  fn maximum_version(&self) -> u64 {
    self.maximum_version.load(Ordering::Acquire)
  }

  #[inline]
  fn minimum_version(&self) -> u64 {
    self.minimum_version.load(Ordering::Acquire)
  }

  #[inline]
  fn height(&self) -> u8 {
    self.height.load(Ordering::Acquire)
  }

  #[inline]
  fn flags(&self) -> Flags {
    self.flags
  }

  #[inline]
  fn len(&self) -> u32 {
    self.len.load(Ordering::Acquire)
  }

  #[inline]
  fn increase_len(&self) {
    self.len.fetch_add(1, Ordering::Release);
  }

  fn update_maximum_version(&self, version: Version) {
    let mut current = self.maximum_version.load(Ordering::Acquire);
    loop {
      if version <= current {
        return;
      }

      match self.maximum_version.compare_exchange_weak(
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

  fn update_minimum_version(&self, version: Version) {
    let mut current = self.minimum_version.load(Ordering::Acquire);
    loop {
      if version >= current {
        return;
      }

      match self.minimum_version.compare_exchange_weak(
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

/// Meta of the skipmap.
#[derive(Debug)]
#[repr(C)]
pub struct Meta {
  len: AtomicU32,
  magic_version: u16,
  /// Current height. 1 <= height <= 31. CAS.
  height: AtomicU8,
  flags: Flags,
}

impl crate::allocator::Meta for Meta {
  #[inline]
  fn new(version: u16) -> Self {
    Self {
      magic_version: version,
      height: AtomicU8::new(1),
      len: AtomicU32::new(0),
      flags: Flags::empty(),
    }
  }

  #[inline]
  fn magic_version(&self) -> u16 {
    self.magic_version
  }

  #[inline]
  fn maximum_version(&self) -> u64 {
    MIN_VERSION
  }

  #[inline]
  fn minimum_version(&self) -> u64 {
    MIN_VERSION
  }

  #[inline]
  fn height(&self) -> u8 {
    self.height.load(Ordering::Acquire)
  }

  #[inline]
  fn flags(&self) -> Flags {
    self.flags
  }

  #[inline]
  fn len(&self) -> u32 {
    self.len.load(Ordering::Acquire)
  }

  #[inline]
  fn increase_len(&self) {
    self.len.fetch_add(1, Ordering::Release);
  }

  fn update_maximum_version(&self, _: Version) {}

  fn update_minimum_version(&self, _: Version) {}

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

  #[inline]
  fn compare_remove(&self, success: Ordering, failure: Ordering) -> Result<(u32, u32), (u32, u32)> {
    let old = self.0.load(Ordering::Acquire);
    let (offset, _) = decode_value_pointer(old);
    let new = encode_value_pointer(offset, Self::REMOVE);
    self
      .0
      .compare_exchange(old, new, success, failure)
      .map(decode_value_pointer)
      .map_err(decode_value_pointer)
  }
}

/// Link to the previous and next node.
#[derive(Debug)]
#[repr(C)]
pub struct Link {
  next_offset: AtomicU32,
  prev_offset: AtomicU32,
}

impl ContainerLink for Link {
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
  ($node: ident {
    $($version_field:ident = $default_version:ident;)?

    {
      fn version(&self) -> Version {
        $($default_version_getter:ident)?
        $({ $getter_this:ident.$version_getter:ident })?
      }
    }
  }) => {
    #[doc(hidden)]
    #[derive(Debug)]
    pub struct NodePointer {
      offset: u32,
      value_ptr: NonNull<<<Self as $crate::allocator::NodePointer>::Node as Node>::ValuePointer>,
      key_offset_ptr: NonNull<u32>,
      key_size_and_height_ptr: NonNull<u32>,
      $($version_field: Version,)?
    }

    impl Clone for NodePointer {
      fn clone(&self) -> Self {
        *self
      }
    }

    impl Copy for NodePointer {}

    impl $crate::allocator::NodePointer for NodePointer {
      const NULL: Self = Self {
        offset: 0,
        value_ptr: NonNull::dangling(),
        key_offset_ptr: NonNull::dangling(),
        key_size_and_height_ptr: NonNull::dangling(),
        $($version_field: $default_version,)?
      };

      type Node = $node;

      #[inline]
      fn is_null(&self) -> bool {
        self.offset == 0
      }

      #[inline]
      fn offset(&self) -> u32 {
        self.offset
      }

      /// ## Safety
      ///
      /// - The caller must ensure that the node is allocated by the arena.
      /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
      unsafe fn next_offset<A: $crate::allocator::Allocator>(&self, arena: &A, idx: usize) -> u32 {
        self.tower(arena, idx).next_offset.load(Ordering::Acquire)
      }

      /// ## Safety
      ///
      /// - The caller must ensure that the node is allocated by the arena.
      /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
      unsafe fn prev_offset<A: $crate::allocator::Allocator>(&self, arena: &A, idx: usize) -> u32 {
        self.tower(arena, idx).prev_offset.load(Ordering::Acquire)
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
      unsafe fn cas_next_offset<A: $crate::allocator::Allocator>(
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
      fn new(
        offset: u32,
        ptr: NonNull<u8>,
      ) -> Self {
        unsafe {
          Self {
            offset,
            value_ptr: ptr.cast(),
            key_offset_ptr: ptr.add(core::mem::size_of::<<Self::Node as Node>::ValuePointer>()).cast(),
            key_size_and_height_ptr: ptr.add(core::mem::size_of::<<Self::Node as Node>::ValuePointer>() + 4).cast(),
            $($version_field: {
              let ptr = ptr.add(core::mem::size_of::<<Self::Node as Node>::ValuePointer>() + 8).cast::<Version>();
              core::ptr::read(ptr.as_ptr())
            },)?
          }
        }
      }

      #[inline]
      fn value_pointer(&self) -> &<Self::Node as Node>::ValuePointer {
        // SAFETY: the pointer is valid, and the value pointer is at the beginning of the node.
        unsafe {
          &*self.value_ptr.as_ptr()
        }
      }

      #[inline]
      fn version(&self) -> Version {
        $($default_version_getter)?
        $(self.$version_getter)?
      }

      #[inline]
      fn set_key_size_and_height(&self, key_size_and_height: u32) {
        // SAFETY: the pointer is valid, and the key size and height is offset 12 to the beginning of the node.
        unsafe {
          let ptr = self.key_size_and_height_ptr.as_ptr();
          *ptr = key_size_and_height;
        }
      }

      #[inline]
      fn set_key_offset(&self, key_offset: u32) {
        // SAFETY: the pointer is valid, and the key size and height is offset 8 to the beginning of the node.
        unsafe {
          let ptr = self.key_offset_ptr.as_ptr();
          *ptr = key_offset;
        }
      }

      #[inline]
      fn key_size_and_height(&self) -> u32 {
        // SAFETY: the pointer is valid, and the key size and height is offset 8 to the beginning of the node.
        unsafe {
          core::ptr::read(self.key_size_and_height_ptr.as_ptr())
        }
      }

      #[inline]
      fn key_offset(&self) -> u32 {
        // SAFETY: the pointer is valid, and the key size and height is offset 8 to the beginning of the node.
        unsafe {
          core::ptr::read(self.key_offset_ptr.as_ptr())
        }
      }
    }
  };
}

/// A skipmap implementation with version support. See [`SkipMap`](multiple_version::SkipMap) for more information.
pub mod multiple_version;

/// A skipmap implementation without version support. See [`SkipMap`](map::SkipMap) for more information.
pub mod map;
