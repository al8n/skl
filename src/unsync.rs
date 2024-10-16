pub use rarena_allocator::unsync::Arena;

use core::cell::UnsafeCell;

use super::{
  allocator::{Link as ContainerLink, *},
  common::*,
  *,
};

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

  #[inline]
  fn compare_remove(&self, _: Ordering, _: Ordering) -> Result<(u32, u32), (u32, u32)> {
    unsafe {
      let ptr = self.0.get();
      let old = *ptr;

      let (offset, size) = decode_value_pointer(old);
      *ptr = encode_value_pointer(offset, Self::REMOVE);

      Ok((offset, size))
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

impl ContainerLink for Link {
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
  ($node: ident $(<$t:ident>)? {
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
    pub struct NodePointer $(<$t: $crate::Trailer>)? {
      offset: u32,
      value_ptr: NonNull<<<Self as $crate::allocator::NodePointer>::Node as Node>::ValuePointer>,
      key_offset_ptr: NonNull<u32>,
      key_size_and_height_ptr: NonNull<u32>,
      $($version_field: Version,)?
      _m: core::marker::PhantomData<$node $(<$t>)?>,
    }

    impl $(<$t: $crate::Trailer>)?  Clone for NodePointer $(<$t>)? {
      fn clone(&self) -> Self {
        *self
      }
    }

    impl $(<$t: $crate::Trailer>)? Copy for NodePointer $(<$t>)? {}

    impl $(<$t: $crate::Trailer>)? $crate::allocator::NodePointer for NodePointer $(<$t>)? {
      const NULL: Self = Self {
        offset: 0,
        value_ptr: NonNull::dangling(),
        key_offset_ptr: NonNull::dangling(),
        key_size_and_height_ptr: NonNull::dangling(),
        $($version_field: $default_version,)?
        _m: core::marker::PhantomData,
      };

      type Node = $node $(<$t>)?;

      #[inline]
      fn is_null(&self) -> bool {
        self.offset == 0
      }

      #[inline]
      fn offset(&self) -> u32 {
        self.offset
      }

      // #[inline]
      // fn pointer(&self) -> &NonNull<u8> {
      //   &self.ptr
      // }

      /// ## Safety
      ///
      /// - The caller must ensure that the node is allocated by the arena.
      /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
      #[inline]
      unsafe fn next_offset<A: $crate::allocator::Allocator>(&self, arena: &A, idx: usize) -> u32 {
        unsafe { *self.tower(arena, idx).next_offset.get() }
      }

      /// ## Safety
      ///
      /// - The caller must ensure that the node is allocated by the arena.
      /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
      #[inline]
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
      fn new(offset: u32, ptr: NonNull<u8>) -> Self {
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
            _m: core::marker::PhantomData,
          }
        }
      }

      // /// ## Safety
      // /// - the pointer must be valid
      // #[inline]
      // unsafe fn as_ref<A: $crate::allocator::Sealed>(&self, arena: &A) -> &Self::Node {
      //   &*(arena.get_pointer(self.offset as usize) as *const Self::Node)
      // }

      // /// ## Safety
      // /// - the pointer must be valid
      // #[inline]
      // unsafe fn as_mut<A: $crate::allocator::Sealed>(&self, arena: &A) -> &mut Self::Node {
      //   &mut *(arena.get_pointer_mut(self.offset as usize) as *mut Self::Node)
      // }

      #[inline]
      fn value_pointer(&self) -> &<Self::Node as Node>::ValuePointer {
        // SAFETY: the pointer is valid, and the value pointer is at the beginning of the node.
        unsafe {
          &*self.value_ptr.as_ptr()
        }
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

      #[inline]
      fn version(&self) -> Version {
        $($default_version_getter)?
        $(self.$version_getter)?
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
