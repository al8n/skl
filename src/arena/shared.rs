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

  #[inline]
  fn as_ptr(&self) -> *const u8 {
    self.ptr.as_ptr()
  }
}

enum SharedBackend {
  Vec(AlignedVec),
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  MmapMut {
    buf: *mut memmap2::MmapMut,
    file: std::fs::File,
    lock: bool,
  },
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  Mmap {
    buf: memmap2::Mmap,
    file: std::fs::File,
    lock: bool,
  },
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  AnonymousMmap(memmap2::MmapMut),
}

pub(super) struct SharedMeta {
  pub(super) height: u8,
  pub(super) len: u32,
  pub(super) max_version: u64,
  pub(super) allocated: u64,
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
  pub(super) fn mmap_mut<P: AsRef<std::path::Path>>(
    cap: usize,
    path: P,
    lock: bool,
  ) -> std::io::Result<Self> {
    use fs4::FileExt;

    let file = std::fs::OpenOptions::new()
      .read(true)
      .write(true)
      .create_new(true)
      .open(path.as_ref())?;
    unsafe {
      if lock {
        file.lock_exclusive()?;
      }

      file.set_len(cap as u64).and_then(|_| {
        memmap2::MmapOptions::new()
          .len(cap)
          .map_mut(&file)
          .map(|mmap| Self {
            cap: cap - MMAP_OVERHEAD,
            backend: SharedBackend::MmapMut {
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
  pub(super) fn mmap<P: AsRef<std::path::Path>>(
    min_cap: usize,
    path: P,
    lock: bool,
  ) -> std::io::Result<(SharedMeta, Self)> {
    use fs4::FileExt;

    let file = std::fs::OpenOptions::new().read(true).open(path.as_ref())?;
    unsafe {
      if lock {
        file.lock_shared()?;
      }

      let allocated = file.metadata()?.len();
      if min_cap as u64 > allocated {
        return Err(std::io::Error::new(
          std::io::ErrorKind::InvalidData,
          "file size is less than the minimum capacity",
        ));
      }

      memmap2::MmapOptions::new()
        .len(allocated as usize)
        .map(&file)
        .and_then(|mmap| {
          let len = mmap.len();
          let cks = crc32fast::hash(&mmap[..len - CHECKSUM_ENCODED_SIZE]);
          let cks2 = u32::from_le_bytes(mmap[len - CHECKSUM_ENCODED_SIZE..len].try_into().unwrap());
          if cks != cks2 {
            return Err(std::io::Error::new(
              std::io::ErrorKind::InvalidData,
              "checksum mismatch",
            ));
          }

          let mut overhead_offset = len - MMAP_OVERHEAD;
          let height = mmap[overhead_offset];
          overhead_offset += HEIGHT_ENCODED_SIZE;
          let len = u32::from_le_bytes(
            mmap[overhead_offset..overhead_offset + LEN_ENCODED_SIZE]
              .try_into()
              .unwrap(),
          );
          overhead_offset += LEN_ENCODED_SIZE;
          let max_version = u64::from_le_bytes(
            mmap[overhead_offset..overhead_offset + MAX_VERSION_ENCODED_SIZE]
              .try_into()
              .unwrap(),
          );

          Ok((
            SharedMeta {
              height,
              len,
              max_version,
              allocated,
            },
            Self {
              cap: allocated as usize,
              backend: SharedBackend::Mmap {
                buf: mmap,
                file,
                lock,
              },
              refs: AtomicUsize::new(1),
            },
          ))
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

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(super) fn flush(&self) -> std::io::Result<()> {
    match &self.backend {
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      SharedBackend::MmapMut { buf: mmap, .. } => unsafe { (**mmap).flush() },
      _ => Ok(()),
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(super) fn flush_async(&self) -> std::io::Result<()> {
    match &self.backend {
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      SharedBackend::MmapMut { buf: mmap, .. } => unsafe { (**mmap).flush_async() },
      _ => Ok(()),
    }
  }

  pub(super) fn as_mut_ptr(&mut self) -> Option<*mut u8> {
    Some(match &mut self.backend {
      SharedBackend::Vec(vec) => vec.as_mut_ptr(),
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      SharedBackend::MmapMut { buf: mmap, .. } => unsafe { (**mmap).as_mut_ptr() },
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      SharedBackend::Mmap { .. } => return None,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      SharedBackend::AnonymousMmap(mmap) => mmap.as_mut_ptr(),
    })
  }

  pub(super) fn as_ptr(&mut self) -> *const u8 {
    match &mut self.backend {
      SharedBackend::Vec(vec) => vec.as_ptr(),
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      SharedBackend::MmapMut { buf: mmap, .. } => unsafe { (**mmap).as_ptr() },
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      SharedBackend::Mmap { buf: mmap, .. } => mmap.as_ptr(),
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      SharedBackend::AnonymousMmap(mmap) => mmap.as_ptr(),
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
  pub(super) unsafe fn unmount(&mut self, _height: u8, _len: u32, _size: u64, _max_version: u64) {
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    match &self.backend {
      SharedBackend::MmapMut { buf, file, lock } => {
        use fs4::FileExt;

        // Any errors during unmapping/closing are ignored as the only way
        // to report them would be through panicking which is highly discouraged
        // in Drop impls, c.f. https://github.com/rust-lang/lang-team/issues/97
        {
          let mmap = &mut **buf;
          let mut cur = _size as usize;
          mmap[cur] = _height;
          cur += HEIGHT_ENCODED_SIZE;
          mmap[cur..cur + LEN_ENCODED_SIZE].copy_from_slice(&_len.to_le_bytes());
          cur += LEN_ENCODED_SIZE;
          mmap[cur..cur + MAX_VERSION_ENCODED_SIZE].copy_from_slice(&_max_version.to_le_bytes());
          cur += MAX_VERSION_ENCODED_SIZE;

          let h = crc32fast::hash(&mmap[..cur]);
          mmap[cur..cur + CHECKSUM_ENCODED_SIZE].copy_from_slice(&h.to_le_bytes());
          let _ = mmap.flush();
        }

        // we must trigger the drop of the mmap before truncating the file
        drop(Box::from_raw(*buf));

        // relaxed ordering is enough here as we're in a drop, no one else can
        // access this memory anymore.
        let actual_size = _size + MMAP_OVERHEAD as u64;
        if actual_size != self.cap as u64 {
          let _ = file.set_len(_size + MMAP_OVERHEAD as u64);
        }

        if *lock {
          let _ = file.unlock();
        }
      }
      SharedBackend::Mmap { lock, file, .. } => {
        use fs4::FileExt;

        // Any errors during unmapping/closing are ignored as the only way
        // to report them would be through panicking which is highly discouraged
        // in Drop impls, c.f. https://github.com/rust-lang/lang-team/issues/97

        // we must trigger the drop of the mmap before truncating the file

        // relaxed ordering is enough here as we're in a drop, no one else can
        // access this memory anymore.
        if *lock {
          let _ = file.unlock();
        }
      }
      _ => {}
    }
  }
}
