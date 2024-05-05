use crate::{
  sync::{AtomicMut, AtomicPtr, Ordering},
  NODE_ALIGNMENT_FACTOR,
};
use core::{
  mem,
  ptr::{self, NonNull},
  slice,
  sync::atomic::AtomicU64,
};
#[allow(unused_imports)]
use std::{boxed::Box, sync::Arc};

use crossbeam_utils::CachePadded;

mod shared;
use shared::Shared;

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
  data_ptr: NonNull<u8>,
  // TODO(al8n): may be move n to `Shared`? then we do not need Arc
  // to make Arena clonable, but not sure which one is better.
  n: Arc<CachePadded<AtomicU64>>,
  inner: AtomicPtr<()>,
  cap: usize,
}

impl core::fmt::Debug for Arena {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    let allocated = self.size();
    // Safety:
    // The ptr is always non-null, we only deallocate it when the arena is dropped.
    let data = unsafe { slice::from_raw_parts(self.data_ptr.as_ptr(), allocated) };
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
}

impl Arena {
  #[inline]
  pub(super) fn new_vec(n: usize, min_cap: usize) -> Self {
    Self::new(Shared::new_vec(
      n.max(min_cap),
      mem::align_of::<u64>().max(NODE_ALIGNMENT_FACTOR),
    ))
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  pub(super) fn new_mmap(
    n: usize,
    min_cap: usize,
    file: std::fs::File,
    lock: bool,
  ) -> std::io::Result<Self> {
    Shared::new_mmaped(n.max(min_cap), file, lock).map(Self::new)
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  pub(super) fn new_anonymous_mmap(n: usize, min_cap: usize) -> std::io::Result<Self> {
    Shared::new_mmaped_anon(n.max(min_cap)).map(Self::new)
  }

  #[inline]
  fn new(mut shared: Shared) -> Self {
    // Safety:
    // The ptr is always non-null, we just initialized it.
    // And this ptr is only deallocated when the arena is dropped.
    let data_ptr = unsafe { NonNull::new_unchecked(shared.as_mut_ptr()) };
    Self {
      cap: shared.cap(),
      inner: AtomicPtr::new(Box::into_raw(Box::new(shared)) as _),
      data_ptr,
      // Don't store data at position 0 in order to reserve offset=0 as a kind
      // of nil pointer.
      n: Arc::new(CachePadded::new(AtomicU64::new(1))),
    }
  }

  #[inline]
  pub(super) fn alloc(
    &self,
    size: u32,
    align: u32,
    overflow: u32,
  ) -> Result<(u32, u32), ArenaError> {
    // Verify that the arena isn't already full.
    let orig_size = self.n.load(Ordering::Acquire);
    if orig_size > self.cap as u64 {
      return Err(ArenaError);
    }

    // Pad the allocation with enough bytes to ensure the requested alignment.
    let padded = size as u64 + align as u64 - 1;

    let new_size = self.n.fetch_add(padded, Ordering::AcqRel) + padded;

    if new_size + overflow as u64 > self.cap as u64 {
      return Err(ArenaError);
    }

    // Return the aligned offset.
    let offset = (new_size as u32 - size) & !(align - 1);

    Ok((offset, padded as u32))
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
    self.data_ptr.as_ptr().add(offset)
  }

  /// ## Safety:
  /// - The caller must make sure that `offset` must be less than the capacity of the arena.
  #[inline]
  pub(super) unsafe fn get_pointer_mut(&self, offset: usize) -> *mut u8 {
    if offset == 0 {
      return ptr::null_mut();
    }
    self.data_ptr.as_ptr().add(offset)
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
        shared.unmount(self.n.load(Ordering::Relaxed) as usize);
      });
    }
  }
}

#[test]
#[cfg(test)]
fn test_debug() {
  let arena = Arena::new_vec(1024, 1024);
  assert_eq!(
    format!("{:?}", arena),
    "Arena { cap: 1024, allocated: 1, data: [0] }"
  );

  let err = ArenaError;
  assert_eq!(
    format!("{}", err),
    "allocation failed because arena is full"
  );
}
