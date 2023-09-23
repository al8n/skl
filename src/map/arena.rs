use crate::{
  error::Error,
  sync::{AtomicMut, AtomicPtr, Ordering},
  Key, KeyTrailer, Value, ValueTrailer,
};
use ::alloc::boxed::Box;
use core::{
  ptr::{self, NonNull},
  slice,
  sync::atomic::AtomicU64,
};

use crossbeam_utils::CachePadded;

use super::node::Node;

mod shared;
use shared::Shared;

/// Arena should be lock-free
pub struct Arena {
  data_ptr: NonNull<u8>,
  n: CachePadded<AtomicU64>,
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
  const fn min_cap<K: KeyTrailer, V: ValueTrailer>() -> usize {
    (Node::<K, V>::MAX_NODE_SIZE * 2) as usize
  }

  #[inline]
  pub(super) fn new_vec<K: Key, V: Value>(n: usize) -> Self {
    Self::new(Shared::new_vec(
      n.max(Self::min_cap::<K::Trailer, V::Trailer>()),
    ))
  }

  #[cfg(feature = "mmap")]
  #[inline]
  pub(super) fn new_mmap<K: Key, V: Value>(
    n: usize,
    file: std::fs::File,
    lock: bool,
  ) -> std::io::Result<Self> {
    Shared::new_mmaped(n.max(Self::min_cap::<K::Trailer, V::Trailer>()), file, lock).map(Self::new)
  }

  #[cfg(feature = "mmap")]
  #[inline]
  pub(super) fn new_anonymous_mmap<K: Key, V: Value>(n: usize) -> std::io::Result<Self> {
    Shared::new_mmaped_anon(n.max(Self::min_cap::<K::Trailer, V::Trailer>())).map(Self::new)
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
      n: CachePadded::new(AtomicU64::new(1)),
    }
  }

  #[inline]
  pub(super) fn alloc(&self, size: u32, align: u32, overflow: u32) -> Result<(u32, u32), Error> {
    // Verify that the arena isn't already full.
    let orig_size = self.n.load(Ordering::Acquire);
    if orig_size > self.cap as u64 {
      return Err(Error::Full);
    }

    // Pad the allocation with enough bytes to ensure the requested alignment.
    let padded = size as u64 + align as u64 - 1;

    let new_size = self.n.fetch_add(padded, Ordering::AcqRel) + padded;

    if new_size + overflow as u64 > self.cap as u64 {
      return Err(Error::Full);
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

  // /// ## Safety:
  // /// - The caller must make sure that `ptr` must be less than the end bound of the arena.
  // #[inline]
  // pub(super) unsafe fn get_pointer_offset(&self, ptr: *const u8) -> usize {
  //   if ptr.is_null() {
  //     return 0;
  //   }

  //   ptr.offset_from(self.data_ptr.as_ptr()) as usize
  // }

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
