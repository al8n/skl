use crate::{
  sync::{AtomicMut, AtomicPtr, AtomicU32, AtomicU64, Ordering},
  NODE_ALIGNMENT_FACTOR,
};
use core::{
  mem,
  ptr::{self, NonNull},
  slice,
};
#[allow(unused_imports)]
use std::boxed::Box;

use crossbeam_utils::CachePadded;

mod shared;
use shared::{Shared, SharedMeta};

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
const HEIGHT_ENCODED_SIZE: usize = mem::size_of::<u8>();

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
const LEN_ENCODED_SIZE: usize = mem::size_of::<u32>();

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
const MAX_VERSION_ENCODED_SIZE: usize = mem::size_of::<u64>();

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
const CHECKSUM_ENCODED_SIZE: usize = mem::size_of::<u32>();

/// The overhead of the memory-mapped file.
///
/// ```text
/// +---------------+------------+--------------------+-----------------+
/// | 8-bit height | 32-bit len | 64-bit max version | 32-bit checksum |
/// +---------------+------------+--------------------+-----------------+
/// ```
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
const MMAP_OVERHEAD: usize =
  HEIGHT_ENCODED_SIZE + LEN_ENCODED_SIZE + MAX_VERSION_ENCODED_SIZE + CHECKSUM_ENCODED_SIZE;

/// An error indicating that the arena is full
#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub struct ArenaError;

impl core::fmt::Display for ArenaError {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    write!(f, "allocation failed because arena is full")
  }
}

#[cfg(feature = "std")]
impl std::error::Error for ArenaError {}

/// Arena should be lock-free
pub struct Arena {
  write_data_ptr: NonNull<u8>,
  read_data_ptr: *const u8,
  n: CachePadded<AtomicU64>,
  /// Current height. 1 <= height <= kMaxHeight. CAS.
  pub(super) height: CachePadded<AtomicU32>,
  pub(super) len: AtomicU32,
  pub(super) max_version: AtomicU64,
  inner: AtomicPtr<()>,
  cap: usize,
}

impl core::fmt::Debug for Arena {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    let allocated = self.size();
    // Safety:
    // The ptr is always non-null, we only deallocate it when the arena is dropped.
    let data = unsafe { slice::from_raw_parts(self.read_data_ptr, allocated) };
    f.debug_struct("Arena")
      .field("cap", &self.cap)
      .field("allocated", &allocated)
      .field("data", &data)
      .finish()
  }
}

impl Arena {
  /// Returns the number of bytes allocated by the arena.
  #[inline]
  pub fn size(&self) -> usize {
    self.n.load(Ordering::Acquire) as usize
  }

  /// Returns the capacity of the arena.
  #[inline]
  pub const fn capacity(&self) -> usize {
    self.cap
  }

  /// Returns the number of bytes remaining bytes can be allocated by the arena.
  #[inline]
  pub fn remaining(&self) -> usize {
    self.cap.saturating_sub(self.size())
  }
}

impl Arena {
  #[inline]
  pub(super) fn new_vec(n: usize, min_cap: usize) -> Self {
    Self::new(
      Shared::new_vec(
        n.max(min_cap),
        mem::align_of::<u64>().max(NODE_ALIGNMENT_FACTOR),
      ),
      None,
    )
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  pub(super) fn mmap_mut<P: AsRef<std::path::Path>>(
    n: usize,
    min_cap: usize,
    path: P,
    lock: bool,
  ) -> std::io::Result<Self> {
    let n = n.saturating_add(MMAP_OVERHEAD);
    Shared::mmap_mut(n.max(min_cap.saturating_add(MMAP_OVERHEAD)), path, lock)
      .map(|shared| Self::new(shared, None))
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  pub(super) fn mmap<P: AsRef<std::path::Path>>(
    min_cap: usize,
    path: P,
    lock: bool,
  ) -> std::io::Result<Self> {
    Shared::mmap(min_cap + MMAP_OVERHEAD, path, lock)
      .map(|(meta, shared)| Self::new(shared, Some(meta)))
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  pub(super) fn new_anonymous_mmap(n: usize, min_cap: usize) -> std::io::Result<Self> {
    Shared::new_mmaped_anon(n.max(min_cap)).map(|shared| Self::new(shared, None))
  }

  #[inline]
  fn head_offset(&self, max_node_size: u32, align: u32) -> u32 {
    // Pad the allocation with enough bytes to ensure the requested alignment.
    let padded = max_node_size as u64 + align as u64 - 1;
    let new_size = 1 + padded;

    // Return the aligned offset.
    (new_size as u32 - max_node_size) & !(align - 1)
  }

  pub(super) fn head_ptr(&self, max_node_size: u32, align: u32) -> (*const u8, u32) {
    // Safety: this method is only invoked when we want a readonly,
    // in readonly mode, we must have the head_ptr valid.
    let offset = self.head_offset(max_node_size, align);
    (unsafe { self.get_pointer(offset as usize) }, offset)
  }

  pub(super) fn tail_ptr(&self, max_node_size: u32, align: u32) -> (*const u8, u32) {
    // Pad the allocation with enough bytes to ensure the requested alignment.
    let padded = max_node_size as u64 + align as u64 - 1;
    let new_size = self.head_offset(max_node_size, align) as u64 + padded + max_node_size as u64;

    // Return the aligned offset.
    let offset = (new_size as u32 - max_node_size) & !(align - 1);

    // Safety: this method is only invoked when we want a readonly,
    // in readonly mode, we must have the head_ptr valid.
    (unsafe { self.get_pointer(offset as usize) }, offset)
  }

  #[inline]
  fn new(mut shared: Shared, meta: Option<SharedMeta>) -> Self {
    // Safety:
    // The ptr is always non-null, we just initialized it.
    // And this ptr is only deallocated when the arena is dropped.
    let read_data_ptr = shared.as_ptr();
    let write_data_ptr = shared
      .as_mut_ptr()
      .map(|p| unsafe { NonNull::new_unchecked(p) })
      .unwrap_or_else(NonNull::dangling);

    let (height, allocated, len, max_version) = match meta {
      Some(meta) => (meta.height, meta.allocated, meta.len, meta.max_version),
      None => {
        let height = 1;
        let len = 0;
        let max_version = 0;
        let allocated = 1;
        (height, allocated, len, max_version)
      }
    };

    Self {
      cap: shared.cap(),
      inner: AtomicPtr::new(Box::into_raw(Box::new(shared)) as _),
      write_data_ptr,
      read_data_ptr,
      height: CachePadded::new(AtomicU32::new(height as u32)),
      len: AtomicU32::new(len),
      // Don't store data at position 0 in order to reserve offset=0 as a kind
      // of nil pointer.
      n: CachePadded::new(AtomicU64::new(allocated)),
      max_version: AtomicU64::new(max_version),
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(super) fn flush(&self) -> std::io::Result<()> {
    let shared = self.inner.load(Ordering::Acquire);
    {
      let shared: *mut Shared = shared.cast();
      unsafe { (*shared).flush() }
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(super) fn flush_async(&self) -> std::io::Result<()> {
    let shared = self.inner.load(Ordering::Acquire);
    {
      let shared: *mut Shared = shared.cast();
      unsafe { (*shared).flush_async() }
    }
  }

  #[inline]
  pub(super) fn alloc(
    &self,
    size: u32,
    align: u32,
    overflow: u32,
  ) -> Result<(u32, u32), ArenaError> {
    // Pad the allocation with enough bytes to ensure the requested alignment.
    let padded = size as u64 + align as u64 - 1;

    let mut current_allocated = self.n.load(Ordering::Acquire);
    if current_allocated + padded + overflow as u64 > self.cap as u64 {
      return Err(ArenaError);
    }

    loop {
      let want = current_allocated + padded;
      match self.n.compare_exchange_weak(
        current_allocated,
        want,
        Ordering::SeqCst,
        Ordering::Acquire,
      ) {
        Ok(current) => {
          // Return the aligned offset.
          let new_size = current + padded;
          let offset = (new_size as u32 - size) & !(align - 1);
          return Ok((offset, padded as u32));
        }
        Err(x) => {
          if x + padded + overflow as u64 > self.cap as u64 {
            return Err(ArenaError);
          }

          current_allocated = x;
        }
      }
    }
  }

  /// ## Safety:
  /// - The caller must make sure that `offset` must be less than the capacity of the arena.
  /// - The caller must make sure that `size` must be less than the capacity of the arena.
  /// - The caller must make sure that `offset + size` must be less than the capacity of the arena.
  #[inline]
  pub(super) unsafe fn get_bytes(&self, offset: usize, size: usize) -> &[u8] {
    if offset == 0 {
      return &[];
    }

    let ptr = self.get_pointer(offset);
    slice::from_raw_parts(ptr, size)
  }

  /// ## Safety:
  /// - The caller must make sure that `offset` must be less than the capacity of the arena.
  /// - The caller must make sure that `size` must be less than the capacity of the arena.
  /// - The caller must make sure that `offset + size` must be less than the capacity of the arena.
  #[allow(clippy::mut_from_ref)]
  #[inline]
  pub(super) unsafe fn get_bytes_mut(&self, offset: usize, size: usize) -> &mut [u8] {
    if offset == 0 {
      return &mut [];
    }

    let ptr = self.get_pointer_mut(offset);
    slice::from_raw_parts_mut(ptr, size)
  }

  /// ## Safety:
  /// - The caller must make sure that `offset` must be less than the capacity of the arena.
  #[inline]
  pub(super) unsafe fn get_pointer(&self, offset: usize) -> *const u8 {
    if offset == 0 {
      return ptr::null();
    }
    self.read_data_ptr.add(offset)
  }

  /// ## Safety:
  /// - The caller must make sure that `offset` must be less than the capacity of the arena.
  #[inline]
  pub(super) unsafe fn get_pointer_mut(&self, offset: usize) -> *mut u8 {
    if offset == 0 {
      return ptr::null_mut();
    }
    self.write_data_ptr.as_ptr().add(offset)
  }
}

impl Drop for Arena {
  fn drop(&mut self) {
    unsafe {
      self.inner.with_mut(|shared| {
        let shared: *mut Shared = shared.cast();
        // `Shared` storage... follow the drop steps from Arc.
        if (*shared).refs.fetch_sub(1, Ordering::Release) != 1 {
          return;
        }

        // This fence is needed to prevent reordering of use of the data and
        // deletion of the data.  Because it is marked `Release`, the decreasing
        // of the reference count synchronizes with this `Acquire` fence. This
        // means that use of the data happens before decreasing the reference
        // count, which happens before this fence, which happens before the
        // deletion of the data.
        //
        // As explained in the [Boost documentation][1],
        //
        // > It is important to enforce any possible access to the object in one
        // > thread (through an existing reference) to *happen before* deleting
        // > the object in a different thread. This is achieved by a "release"
        // > operation after dropping a reference (any access to the object
        // > through this reference must obviously happened before), and an
        // > "acquire" operation before deleting the object.
        //
        // [1]: (www.boost.org/doc/libs/1_55_0/doc/html/atomic/usage_examples.html)
        //
        // Thread sanitizer does not support atomic fences. Use an atomic load
        // instead.
        (*shared).refs.load(Ordering::Acquire);
        // Drop the data
        let mut shared = Box::from_raw(shared);

        // Relaxed is enough here as we're in a drop, no one else can
        // access this memory anymore.
        shared.unmount(
          self.height.load(Ordering::Acquire) as u8,
          self.len.load(Ordering::Acquire),
          self.n.load(Ordering::Acquire),
          self.max_version.load(Ordering::Acquire),
        );
      });
    }
  }
}

#[test]
#[cfg(test)]
fn test_debug() {
  let arena = Arena::new_vec(1024, 1024);
  assert_eq!(
    std::format!("{:?}", arena),
    "Arena { cap: 1024, allocated: 1, data: [0] }"
  );

  let err = ArenaError;
  assert_eq!(
    std::format!("{}", err),
    "allocation failed because arena is full"
  );
}
