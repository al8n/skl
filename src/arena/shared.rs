use super::*;

use crate::sync::AtomicUsize;

#[derive(Debug)]
struct AlignedVec {
  ptr: ptr::NonNull<u8>,
  cap: usize,
  align: usize,
}

impl Drop for AlignedVec {
  #[inline]
  fn drop(&mut self) {
    if self.cap != 0 {
      unsafe {
        std::alloc::dealloc(self.ptr.as_ptr(), self.layout());
      }
    }
  }
}

impl AlignedVec {
  #[inline]
  fn new(capacity: usize, align: usize) -> Self {
    assert!(
      capacity <= Self::max_capacity(align),
      "`capacity` cannot exceed isize::MAX - {}",
      align - 1
    );
    let ptr = unsafe {
      let layout = std::alloc::Layout::from_size_align_unchecked(capacity, align);
      let ptr = std::alloc::alloc(layout);
      if ptr.is_null() {
        std::alloc::handle_alloc_error(layout);
      }
      ptr::NonNull::new_unchecked(ptr)
    };

    unsafe {
      core::ptr::write_bytes(ptr.as_ptr(), 0, capacity);
    }
    Self {
      ptr,
      cap: capacity,
      align,
    }
  }

  #[inline]
  const fn max_capacity(align: usize) -> usize {
    isize::MAX as usize - (align - 1)
  }

  #[inline]
  fn layout(&self) -> std::alloc::Layout {
    unsafe { std::alloc::Layout::from_size_align_unchecked(self.cap, self.align) }
  }

  #[inline]
  fn as_mut_ptr(&mut self) -> *mut u8 {
    self.ptr.as_ptr()
  }
}

enum SharedBackend {
  Vec(AlignedVec),
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  Mmap {
    buf: *mut memmap2::MmapMut,
    file: std::fs::File,
    lock: bool,
  },
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  AnonymousMmap(memmap2::MmapMut),
}

pub(super) struct Shared {
  pub(super) refs: AtomicUsize,
  cap: usize,
  backend: SharedBackend,
}

impl Shared {
  pub(super) fn new_vec(cap: usize, align: usize) -> Self {
    let vec = AlignedVec::new(cap, align);
    Self {
      cap: vec.cap,
      backend: SharedBackend::Vec(vec),
      refs: AtomicUsize::new(1),
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
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
          .map(|mmap| Self {
            cap,
            backend: SharedBackend::Mmap {
              buf: Box::into_raw(Box::new(mmap)),
              file,
              lock,
            },
            refs: AtomicUsize::new(1),
          })
      })
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(super) fn new_mmaped_anon(cap: usize) -> std::io::Result<Self> {
    memmap2::MmapOptions::new()
      .len(cap)
      .map_anon()
      .map(|mmap| Self {
        cap,
        backend: SharedBackend::AnonymousMmap(mmap),
        refs: AtomicUsize::new(1),
      })
  }

  pub(super) fn as_mut_ptr(&mut self) -> *mut u8 {
    match &mut self.backend {
      SharedBackend::Vec(vec) => vec.as_mut_ptr(),
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      SharedBackend::Mmap { buf: mmap, .. } => unsafe { (**mmap).as_mut_ptr() },
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      SharedBackend::AnonymousMmap(mmap) => mmap.as_mut_ptr(),
    }
  }

  #[inline]
  pub(super) const fn cap(&self) -> usize {
    self.cap
  }

  /// Only works on mmap with a file backend, unmounts the memory mapped file and truncates it to the specified size.
  ///
  /// ## Safety:
  /// - This method must be invoked in the drop impl of `Arena`.
  pub(super) unsafe fn unmount(&mut self, _size: usize) {
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    if let SharedBackend::Mmap { buf, file, lock } = &self.backend {
      use fs4::FileExt;

      // Any errors during unmapping/closing are ignored as the only way
      // to report them would be through panicking which is highly discouraged
      // in Drop impls, c.f. https://github.com/rust-lang/lang-team/issues/97

      {
        let mmap = &**buf;
        let _ = mmap.flush();
      }

      // we must trigger the drop of the mmap before truncating the file
      drop(Box::from_raw(*buf));

      // relaxed ordering is enough here as we're in a drop, no one else can
      // access this memory anymore.
      let _ = file.set_len(_size as u64);
      if *lock {
        let _ = file.unlock();
      }
    }
  }
}
