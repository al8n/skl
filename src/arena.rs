use crate::sync::{AtomicMut, AtomicPtr, AtomicU32, AtomicU64, Ordering};
use core::{
  mem,
  ptr::{self, NonNull},
  slice,
};
#[allow(unused_imports)]
use std::boxed::Box;

use crossbeam_utils::CachePadded;

mod shared;
use shared::Shared;

/// The overhead of the memory-mapped file.
///
/// ```text
/// +---------------+------------+--------------------+--------------------+
/// | 32-bit height  | 32-bit len | 64-bit max version | 64-bit min version |
/// +---------------+------------+--------------------+--------------------+
/// ```
const MMAP_OVERHEAD: usize = mem::size_of::<Header>();

#[derive(Debug)]
#[repr(C)]
pub(super) struct Header {
  /// Current height. 1 <= height <= kMaxHeight. CAS.
  height: AtomicU32,
  len: AtomicU32,
  max_version: AtomicU64,
  min_version: AtomicU64,
}

impl Default for Header {
  fn default() -> Self {
    Self {
      height: AtomicU32::new(1),
      len: AtomicU32::new(0),
      max_version: AtomicU64::new(0),
      min_version: AtomicU64::new(0),
    }
  }
}

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
  header_ptr: *const Header,
  data_offset: u64,
  n: CachePadded<AtomicU64>,
  inner: AtomicPtr<()>,
  cap: usize,
}

impl core::fmt::Debug for Arena {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    let allocated = self.size();
    // Safety:
    // The ptr is always non-null, we only deallocate it when the arena is dropped.
    let data =
      unsafe { slice::from_raw_parts(self.read_data_ptr, allocated - self.data_offset as usize) };
    let header = self.header();
    f.debug_struct("Arena")
      .field("cap", &self.cap)
      .field("allocated", &allocated)
      .field("header", header)
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

  /// Returns the height of the arena.
  #[inline]
  pub fn height(&self) -> u32 {
    self.header().height.load(Ordering::Acquire)
  }

  /// Returns the length of the arena.
  #[inline]
  pub(super) fn len(&self) -> u32 {
    self.header().len.load(Ordering::Acquire)
  }

  /// Returns the max version of the arena.
  #[inline]
  pub fn max_version(&self) -> u64 {
    self.header().max_version.load(Ordering::Acquire)
  }

  /// Returns the min version of the arena.
  #[inline]
  pub fn min_version(&self) -> u64 {
    self.header().min_version.load(Ordering::Acquire)
  }

  #[inline]
  pub(super) const fn atomic_height(&self) -> &AtomicU32 {
    &self.header().height
  }

  #[inline]
  pub(super) fn incr_len(&self) {
    self.header().len.fetch_add(1, Ordering::Release);
  }

  pub(super) fn update_max_version(&self, version: u64) {
    let mut current = self.header().max_version.load(Ordering::Acquire);

    loop {
      if version <= current {
        return;
      }

      match self.header().max_version.compare_exchange_weak(
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

  pub(super) fn update_min_version(&self, version: u64) {
    let mut current = self.header().min_version.load(Ordering::Acquire);

    loop {
      if version >= current {
        return;
      }

      match self.header().min_version.compare_exchange_weak(
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
  pub(super) const fn header(&self) -> &Header {
    // Safety:
    // The header is always non-null, we only deallocate it when the arena is dropped.
    unsafe { &*self.header_ptr }
  }

  #[inline]
  pub(crate) fn clear(&self) {
    let header = self.header();
    header.len.store(0, Ordering::Release);
    header.height.store(1, Ordering::Release);
    header.max_version.store(0, Ordering::Release);
    header.min_version.store(0, Ordering::Release);
  }
}

impl Arena {
  #[inline]
  pub(super) fn new_vec(n: usize, min_cap: usize, alignment: usize) -> Self {
    Self::new(
      Shared::new_vec(n.max(min_cap.saturating_add(MMAP_OVERHEAD)), alignment),
      None,
    )
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  pub(super) fn mmap_mut<P: AsRef<std::path::Path>>(
    path: P,
    n: usize,
    min_cap: usize,
    alignment: usize,
    lock: bool,
  ) -> std::io::Result<Self> {
    let n = n.saturating_add(MMAP_OVERHEAD);
    Shared::mmap_mut(
      n.max(min_cap.saturating_add(MMAP_OVERHEAD)),
      path,
      alignment,
      lock,
    )
    .map(|shared| Self::new(shared, None))
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  pub(super) fn mmap<P: AsRef<std::path::Path>>(
    path: P,
    min_cap: usize,
    alignment: usize,
    lock: bool,
  ) -> std::io::Result<Self> {
    Shared::mmap(min_cap.saturating_add(MMAP_OVERHEAD), alignment, path, lock)
      .map(|(allocated, shared)| Self::new(shared, Some(allocated)))
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  pub(super) fn new_anonymous_mmap(
    n: usize,
    min_cap: usize,
    alignment: usize,
  ) -> std::io::Result<Self> {
    Shared::new_mmaped_anon(n.max(min_cap.saturating_add(MMAP_OVERHEAD)), alignment)
      .map(|shared| Self::new(shared, None))
  }

  #[inline]
  fn head_offset(&self, max_node_size: u32, align: u32) -> u32 {
    // Pad the allocation with enough bytes to ensure the requested alignment.
    let padded = max_node_size as u64 + align as u64 - 1;
    let new_size = 1 + self.data_offset + padded;

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
  fn new(mut shared: Shared, allocated: Option<u64>) -> Self {
    // Safety:
    // The ptr is always non-null, we just initialized it.
    // And this ptr is only deallocated when the arena is dropped.
    let read_data_ptr = shared.as_ptr();
    let header_ptr = shared.header_ptr();
    let write_data_ptr = shared
      .as_mut_ptr()
      .map(|p| unsafe { NonNull::new_unchecked(p) })
      .unwrap_or_else(NonNull::dangling);
    let data_offset = shared.data_offset as u64;
    let allocated = allocated.unwrap_or(1u64 + data_offset);

    Self {
      cap: shared.cap(),
      inner: AtomicPtr::new(Box::into_raw(Box::new(shared)) as _),
      write_data_ptr,
      read_data_ptr,
      header_ptr,
      // Don't store data at position 0 in order to reserve offset=0 as a kind
      // of nil pointer.
      n: CachePadded::new(AtomicU64::new(allocated)),
      data_offset,
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
        shared.unmount(self.n.load(Ordering::Acquire));
      });
    }
  }
}

#[test]
#[cfg(test)]
fn test_debug() {
  let arena = Arena::new_vec(1024, 1024, 8);
  assert_eq!(
    std::format!("{:?}", arena),
    "Arena { cap: 1048, allocated: 25, header: Header { height: 1, len: 0, max_version: 0, min_version: 0 }, data: [0] }"
  );

  let err = ArenaError;
  assert_eq!(
    std::format!("{}", err),
    "allocation failed because arena is full"
  );
}
