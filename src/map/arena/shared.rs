use std::alloc;

use core::ops::{Index, IndexMut};

use crate::sync::AtomicUsize;

use super::*;

#[derive(Debug)]
struct AlignedVec {
  ptr: ptr::NonNull<u8>,
  cap: usize,
  len: usize,
}

impl Drop for AlignedVec {
  #[inline]
  fn drop(&mut self) {
    if self.cap != 0 {
      unsafe {
        alloc::dealloc(self.ptr.as_ptr(), self.layout());
      }
    }
  }
}

impl AlignedVec {
  const ALIGNMENT: usize = core::mem::align_of::<Node>();

  const MAX_CAPACITY: usize = isize::MAX as usize - (Self::ALIGNMENT - 1);

  #[inline]
  fn new(capacity: usize) -> Self {
    assert!(
      capacity <= Self::MAX_CAPACITY,
      "`capacity` cannot exceed isize::MAX - {}",
      Self::ALIGNMENT - 1
    );
    let ptr = unsafe {
      let layout = alloc::Layout::from_size_align_unchecked(capacity, Self::ALIGNMENT);
      let ptr = alloc::alloc(layout);
      if ptr.is_null() {
        alloc::handle_alloc_error(layout);
      }
      ptr::NonNull::new_unchecked(ptr)
    };

    unsafe {
      core::ptr::write_bytes(ptr.as_ptr(), 0, capacity);
    }
    Self {
      ptr,
      cap: capacity,
      len: capacity,
    }
  }

  #[inline]
  fn layout(&self) -> alloc::Layout {
    unsafe { alloc::Layout::from_size_align_unchecked(self.cap, Self::ALIGNMENT) }
  }

  #[inline]
  fn as_mut_ptr(&mut self) -> *mut u8 {
    self.ptr.as_ptr()
  }

  #[inline]
  const fn as_slice(&self) -> &[u8] {
    unsafe { slice::from_raw_parts(self.ptr.as_ptr(), self.len) }
  }

  #[inline]
  fn as_mut_slice(&mut self) -> &mut [u8] {
    unsafe { slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len) }
  }
}

impl<I: slice::SliceIndex<[u8]>> Index<I> for AlignedVec {
  type Output = <I as slice::SliceIndex<[u8]>>::Output;

  #[inline]
  fn index(&self, index: I) -> &Self::Output {
    &self.as_slice()[index]
  }
}

impl<I: slice::SliceIndex<[u8]>> IndexMut<I> for AlignedVec {
  #[inline]
  fn index_mut(&mut self, index: I) -> &mut Self::Output {
    &mut self.as_mut_slice()[index]
  }
}

enum SharedBackend {
  Vec(AlignedVec),
  #[cfg(all(feature = "mmap", not(target_family = "wasm")))]
  Mmap {
    buf: *mut memmap2::MmapMut,
    file: std::fs::File,
    lock: bool,
  },
  #[cfg(all(feature = "mmap", not(target_family = "wasm")))]
  AnonymousMmap(memmap2::MmapMut),
}

pub(super) struct Shared {
  pub(super) n: AtomicU32,
  pub(super) refs: AtomicUsize,
  cap: usize,
  backend: SharedBackend,
}

impl Shared {
  pub(super) fn new_vec(cap: usize) -> Self {
    let vec = AlignedVec::new(cap);
    Self {
      cap: vec.cap,
      backend: SharedBackend::Vec(vec),
      refs: AtomicUsize::new(1),
      // Don't store data at position 0 in order to reserve offset=0 as a kind
      // of nil pointer.
      n: AtomicU32::new(1),
    }
  }

  #[cfg(all(feature = "mmap", not(target_family = "wasm")))]
  pub(super) fn new_mmaped(cap: usize, file: std::fs::File, lock: bool) -> std::io::Result<Self> {
    use fs4::FileExt;

    unsafe {
      if lock {
        file.lock_exclusive()?;
      }

      file.set_len(cap as u64).and_then(|_| {
        memmap2::MmapOptions::new()
          .len(cap)
          .map_mut(&file)
          .map(|mmap| {
            Self {
              cap,
              backend: SharedBackend::Mmap {
                buf: Box::into_raw(Box::new(mmap)),
                file,
                lock,
              },
              refs: AtomicUsize::new(1),
              // Don't store data at position 0 in order to reserve offset=0 as a kind
              // of nil pointer.
              n: AtomicU32::new(1),
            }
          })
      })
    }
  }

  #[cfg(all(feature = "mmap", not(target_family = "wasm")))]
  pub(super) fn new_mmaped_anon(cap: usize) -> std::io::Result<Self> {
    memmap2::MmapOptions::new().len(cap).map_anon().map(|mmap| {
      Self {
        cap,
        backend: SharedBackend::AnonymousMmap(mmap),
        refs: AtomicUsize::new(1),
        // Don't store data at position 0 in order to reserve offset=0 as a kind
        // of nil pointer.
        n: AtomicU32::new(1),
      }
    })
  }

  pub(super) fn as_slice(&self) -> &[u8] {
    let end = self.n.load(Ordering::Acquire) as usize;
    match &self.backend {
      SharedBackend::Vec(vec) => &vec.as_slice()[..end],
      #[cfg(all(feature = "mmap", not(target_family = "wasm")))]
      SharedBackend::Mmap { buf: mmap, .. } => unsafe { &(&**mmap)[..end] },
      #[cfg(all(feature = "mmap", not(target_family = "wasm")))]
      SharedBackend::AnonymousMmap(mmap) => &mmap[..end],
    }
  }

  pub(super) fn as_mut_ptr(&mut self) -> *mut u8 {
    match &mut self.backend {
      SharedBackend::Vec(vec) => vec.as_mut_ptr(),
      #[cfg(all(feature = "mmap", not(target_family = "wasm")))]
      SharedBackend::Mmap { buf: mmap, .. } => unsafe { (**mmap).as_mut_ptr() },
      #[cfg(all(feature = "mmap", not(target_family = "wasm")))]
      SharedBackend::AnonymousMmap(mmap) => mmap.as_mut_ptr(),
    }
  }

  #[inline]
  pub(super) const fn cap(&self) -> usize {
    self.cap
  }
}

impl Drop for Shared {
  fn drop(&mut self) {
    #[cfg(all(feature = "mmap", not(target_family = "wasm")))]
    if let SharedBackend::Mmap { buf, file, lock } = &self.backend {
      use fs4::FileExt;

      // Any errors during unmapping/closing are ignored as the only way
      // to report them would be through panicking which is highly discouraged
      // in Drop impls, c.f. https://github.com/rust-lang/lang-team/issues/97

      unsafe {
        {
          let mmap = &**buf;
          let _ = mmap.flush();
        }

        // we must trigger the drop of the mmap before truncating the file
        let _ = Box::from_raw(*buf);

        // relaxed ordering is enough here as we're in a drop, no one else can
        // access this memory anymore.
        let size = self.n.load(Ordering::Relaxed);
        let _ = file.set_len(size as u64);
        if *lock {
          let _ = file.unlock();
        }
      }
    }
  }
}
