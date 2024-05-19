use crate::sync::{AtomicPtr, AtomicU32, AtomicU64, Ordering};
#[allow(unused_imports)]
use std::boxed::Box;

#[cfg(not(loom))]
use crate::sync::AtomicMut;

use core::{
  mem,
  ptr::{self, NonNull},
  slice,
};

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
use crate::{invalid_data, MmapOptions, OpenOptions};

mod shared;
use shared::Shared;

/// The overhead of the memory-mapped file.
///
/// ```text
/// +----------------+------------+--------------------+--------------------+---------------------+
/// | 32-bit height  | 32-bit len | 64-bit max version | 64-bit min version | 64-bit allocated    |
/// +----------------+------------+--------------------+--------------------+---------------------+
/// ```
const MMAP_OVERHEAD: usize = mem::size_of::<Header>();

#[derive(Debug)]
#[repr(C, align(8))]
pub(super) struct Header {
  max_version: AtomicU64,
  min_version: AtomicU64,
  allocated: AtomicU64,
  /// Current height. 1 <= height <= kMaxHeight. CAS.
  height: AtomicU32,
  len: AtomicU32,

  discard: AtomicU32,

  // Reserved for segmented list.
  segmented_head_ptr: AtomicU32,
  segmented_tail_ptr: AtomicU32,
}

impl Header {
  fn new(size: u64) -> Self {
    Self {
      height: AtomicU32::new(1),
      len: AtomicU32::new(0),
      max_version: AtomicU64::new(0),
      min_version: AtomicU64::new(0),
      // Don't store data at position 0 in order to reserve offset=0 as a kind
      // of nil pointer.
      allocated: AtomicU64::new(size + 1),
      discard: AtomicU32::new(0),
      segmented_head_ptr: AtomicU32::new(0),
      segmented_tail_ptr: AtomicU32::new(0),
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
      .field("header", header)
      .field("data", &data)
      .finish()
  }
}

impl Clone for Arena {
  fn clone(&self) -> Self {
    unsafe {
      let shared: *mut Shared = self.inner.load(Ordering::Relaxed).cast();

      let old_size = (*shared).refs.fetch_add(1, Ordering::Release);
      if old_size > usize::MAX >> 1 {
        abort();
      }

      // Safety:
      // The ptr is always non-null, and the data is only deallocated when the
      // last Arena is dropped.
      Self {
        write_data_ptr: self.write_data_ptr,
        read_data_ptr: self.read_data_ptr,
        header_ptr: self.header_ptr,
        data_offset: self.data_offset,
        inner: AtomicPtr::new(shared as _),
        cap: self.cap,
      }
    }
  }
}

#[inline(never)]
#[cold]
fn abort() -> ! {
  #[cfg(feature = "std")]
  {
    std::process::abort()
  }

  #[cfg(not(feature = "std"))]
  {
    struct Abort;
    impl Drop for Abort {
      fn drop(&mut self) {
        panic!();
      }
    }
    let _a = Abort;
    panic!("abort");
  }
}

impl Arena {
  /// Returns the number of bytes allocated by the arena.
  #[inline]
  pub fn size(&self) -> usize {
    self.header().allocated.load(Ordering::Acquire) as usize
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
  pub(super) fn discard(&self) -> u32 {
    self.header().discard.load(Ordering::Acquire)
  }

  #[inline]
  pub(super) fn incr_len(&self) {
    self.header().len.fetch_add(1, Ordering::Release);
  }

  #[inline]
  pub(super) fn incr_discard(&self, size: u32) {
    self.header().discard.fetch_add(size, Ordering::Release);
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
    Self::new(Shared::new_vec(
      n.max(min_cap.saturating_add(MMAP_OVERHEAD)),
      alignment.max(8),
    ))
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  pub(super) fn mmap_mut<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    min_cap: usize,
    alignment: usize,
  ) -> std::io::Result<Self> {
    let min_cap = min_cap.saturating_add(MMAP_OVERHEAD);
    Shared::mmap_mut(path, open_options, mmap_options, min_cap, alignment).map(Self::new)
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  pub(super) fn mmap<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    min_cap: usize,
    alignment: usize,
  ) -> std::io::Result<Self> {
    let min_cap = min_cap.saturating_add(MMAP_OVERHEAD);
    Shared::mmap(path, open_options, mmap_options, min_cap, alignment).map(Self::new)
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  pub(super) fn new_anonymous_mmap(
    mmap_options: MmapOptions,
    min_cap: usize,
    alignment: usize,
  ) -> std::io::Result<Self> {
    let min_cap = min_cap.saturating_add(MMAP_OVERHEAD);
    Shared::new_mmaped_anon(mmap_options, min_cap, alignment).map(Self::new)
  }

  #[inline]
  fn head_offset<T>(&self, max_node_size: u32, align: u32) -> (u32, u32) {
    let trailer_size = mem::size_of::<T>();
    let trailer_align = mem::align_of::<T>();

    // Pad the allocation with enough bytes to ensure the requested alignment.
    let padded = max_node_size as u64 + align as u64 - 1;
    let trailer_padded = trailer_size as u64 + trailer_align as u64 - 1;
    let allocated = 1 + self.data_offset + padded;

    // Return the aligned offset.
    let node_offset = (allocated as u32 - max_node_size) & !(align - 1);
    let total_allocated = allocated + trailer_padded;
    (node_offset, total_allocated as u32)
  }

  pub(super) fn head_ptr<T>(&self, max_node_size: u32, align: u32) -> (*const u8, u32) {
    // Safety: this method is only invoked when we want a readonly,
    // in readonly mode, we must have the head_ptr valid.
    let (offset, _) = self.head_offset::<T>(max_node_size, align);
    (unsafe { self.get_pointer(offset as usize) }, offset)
  }

  pub(super) fn tail_ptr<T>(&self, max_node_size: u32, align: u32) -> (*const u8, u32) {
    // Pad the allocation with enough bytes to ensure the requested alignment.
    let padded = max_node_size as u64 + align as u64 - 1;
    let (_, current_allocated) = self.head_offset::<T>(max_node_size, align);

    let allocated = current_allocated as u64 + padded;
    let offset = (allocated as u32 - max_node_size) & !(align - 1);

    // Safety: this method is only invoked when we want a readonly,
    // in readonly mode, we must have the head_ptr valid.
    (unsafe { self.get_pointer(offset as usize) }, offset)
  }

  #[inline]
  fn new(mut shared: Shared) -> Self {
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

    Self {
      cap: shared.cap(),
      inner: AtomicPtr::new(Box::into_raw(Box::new(shared)) as _),
      write_data_ptr,
      read_data_ptr,
      header_ptr,
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

  #[cfg(not(feature = "unaligned"))]
  pub(super) fn alloc<T>(
    &self,
    size: u32,
    value_size: u32,
    align: u32,
    overflow: u32,
  ) -> Result<AllocMeta, ArenaError> {
    let trailer_size = mem::size_of::<T>();
    let trailer_align = mem::align_of::<T>();

    // Pad the allocation with enough bytes to ensure the requested alignment.
    let padded = size as u64 + align as u64 - 1;
    let trailer_padded = trailer_size as u64 + trailer_align as u64 - 1;
    let header = self.header();
    let mut current_allocated = header.allocated.load(Ordering::Acquire);
    if current_allocated + padded + overflow as u64 + trailer_padded + value_size as u64
      > self.cap as u64
    {
      return Err(ArenaError);
    }

    loop {
      let want = current_allocated + padded + trailer_padded + value_size as u64;
      match header.allocated.compare_exchange_weak(
        current_allocated,
        want,
        Ordering::SeqCst,
        Ordering::Acquire,
      ) {
        Ok(current) => {
          // Return the aligned offset.
          let allocated = current + padded;
          let node_offset = (allocated as u32 - size) & !(align - 1);

          let allocated_for_trailer = allocated + trailer_padded;
          let value_offset =
            (allocated_for_trailer as u32 - trailer_size as u32) & !(trailer_align as u32 - 1);

          return Ok(AllocMeta {
            node_offset,
            value_offset,
            allocated: (padded + trailer_padded + value_size as u64) as u32,
          });
        }
        Err(x) => {
          if x + padded + overflow as u64 + trailer_padded + value_size as u64 > self.cap as u64 {
            return Err(ArenaError);
          }

          current_allocated = x;
        }
      }
    }
  }

  #[cfg(not(feature = "unaligned"))]
  pub(super) fn alloc_value<T>(&self, size: u32) -> Result<u32, ArenaError> {
    let trailer_size = mem::size_of::<T>();
    let align = mem::align_of::<T>();
    let size = size + trailer_size as u32;
    let padded = size as u64 + align as u64 - 1;

    let header = self.header();
    let mut current_allocated = header.allocated.load(Ordering::Acquire);
    if current_allocated + padded > self.cap as u64 {
      return Err(ArenaError);
    }

    loop {
      let want = current_allocated + padded;
      match header.allocated.compare_exchange_weak(
        current_allocated,
        want,
        Ordering::SeqCst,
        Ordering::Acquire,
      ) {
        Ok(current) => {
          // Return the aligned offset.
          let allocated = current + padded;
          let value_offset = (allocated as u32 - size) & !(align as u32 - 1);
          return Ok(value_offset);
        }
        Err(x) => {
          if x + padded > self.cap as u64 {
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
  pub(super) const unsafe fn get_bytes(&self, offset: usize, size: usize) -> &[u8] {
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
  pub(super) const unsafe fn get_pointer(&self, offset: usize) -> *const u8 {
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
        shared.unmount();
      });
    }
  }
}

pub(crate) struct AllocMeta {
  pub(crate) node_offset: u32,
  pub(crate) value_offset: u32,
  pub(crate) allocated: u32,
}

#[test]
#[cfg(all(not(loom), test))]
fn test_debug() {
  let arena = Arena::new_vec(1024, 1024, 8);
  assert_eq!(
    std::format!("{:?}", arena),
    "Arena { cap: 1064, header: Header { max_version: 0, min_version: 0, allocated: 41, height: 1, len: 0, segmented_head_ptr: 0, segmented_tail_ptr: 0 }, data: [0] }"
  );

  let err = ArenaError;
  assert_eq!(
    std::format!("{}", err),
    "allocation failed because arena is full"
  );
}
