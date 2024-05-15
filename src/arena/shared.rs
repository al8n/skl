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
    shrink_on_drop: bool,
  },
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  Mmap {
    buf: *mut memmap2::Mmap,
    file: std::fs::File,
    lock: bool,
    shrink_on_drop: bool,
  },
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  AnonymousMmap(memmap2::MmapMut),
}

const fn data_offset(alignment: usize) -> usize {
  let header_size = mem::size_of::<Header>();
  let offset = (alignment - (header_size % alignment)) % alignment;
  header_size + offset
}

pub(super) struct Shared {
  pub(super) refs: AtomicUsize,
  cap: usize,
  pub(super) data_offset: usize,
  backend: SharedBackend,
}

impl Shared {
  pub(super) fn new_vec(cap: usize, alignment: usize) -> Self {
    let vec = AlignedVec::new(cap, alignment);
    let this = Self {
      cap: vec.cap,
      backend: SharedBackend::Vec(vec),
      refs: AtomicUsize::new(1),
      data_offset: data_offset(alignment),
    };
    // Safety: we have add the overhead for the header
    unsafe {
      this
        .header_mut_ptr()
        .write(Header::new(this.data_offset as u64));
    }
    this
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(super) fn mmap_mut<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    min_cap: usize,
    alignment: usize,
  ) -> std::io::Result<Self> {
    let file = open_options.open(path.as_ref())?;

    unsafe {
      mmap_options.map_mut(&file).and_then(|mmap| {
        let cap = mmap.len();
        if cap < min_cap {
          return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "file size is less than the minimum capacity",
          ));
        }
        let this = Self {
          cap,
          backend: SharedBackend::MmapMut {
            buf: Box::into_raw(Box::new(mmap)),
            file,
            lock: open_options.is_lock(),
            shrink_on_drop: open_options.is_shrink_on_drop(),
          },
          refs: AtomicUsize::new(1),
          data_offset: data_offset(alignment),
        };
        // Safety: we have add the overhead for the header
        this
          .header_mut_ptr()
          .write(Header::new(this.data_offset as u64));

        Ok(this)
      })
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(super) fn mmap<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    min_cap: usize,
    alignment: usize,
  ) -> std::io::Result<Self> {
    let file = open_options.open(path.as_ref())?;
    unsafe {
      mmap_options.map(&file).and_then(|mmap| {
        let len = mmap.len();
        if len < min_cap {
          return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "file size is less than the minimum capacity",
          ));
        }

        Ok(Self {
          cap: len,
          backend: SharedBackend::Mmap {
            buf: Box::into_raw(Box::new(mmap)),
            file,
            lock: open_options.is_lock(),
            shrink_on_drop: open_options.is_shrink_on_drop(),
          },
          refs: AtomicUsize::new(1),
          data_offset: data_offset(alignment),
        })
      })
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(super) fn new_mmaped_anon(
    mmap_options: MmapOptions,
    min_cap: usize,
    alignment: usize,
  ) -> std::io::Result<Self> {
    mmap_options.map_anon().and_then(|mmap| {
      if mmap.len() < min_cap {
        return Err(std::io::Error::new(
          std::io::ErrorKind::InvalidData,
          "file size is less than the minimum capacity",
        ));
      }

      let this = Self {
        cap: mmap.len(),
        backend: SharedBackend::AnonymousMmap(mmap),
        refs: AtomicUsize::new(1),
        data_offset: data_offset(alignment),
      };
      // Safety: we have add the overhead for the header
      unsafe {
        this
          .header_mut_ptr()
          .write(Header::new(this.data_offset as u64));
      }
      Ok(this)
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

  #[inline]
  pub(super) fn as_mut_ptr(&mut self) -> Option<*mut u8> {
    unsafe {
      Some(match &mut self.backend {
        SharedBackend::Vec(vec) => vec.as_mut_ptr().add(self.data_offset),
        #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
        SharedBackend::MmapMut { buf: mmap, .. } => (**mmap).as_mut_ptr().add(self.data_offset),
        #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
        SharedBackend::Mmap { .. } => return None,
        #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
        SharedBackend::AnonymousMmap(mmap) => mmap.as_mut_ptr().add(self.data_offset),
      })
    }
  }

  #[inline]
  pub(super) fn as_ptr(&self) -> *const u8 {
    unsafe {
      match &self.backend {
        SharedBackend::Vec(vec) => vec.as_ptr().add(self.data_offset),
        #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
        SharedBackend::MmapMut { buf: mmap, .. } => (**mmap).as_ptr().add(self.data_offset),
        #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
        SharedBackend::Mmap { buf: mmap, .. } => (**mmap).as_ptr().add(self.data_offset),
        #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
        SharedBackend::AnonymousMmap(mmap) => mmap.as_ptr().add(self.data_offset),
      }
    }
  }

  #[inline]
  pub(super) fn header_ptr(&self) -> *const Header {
    match &self.backend {
      SharedBackend::Vec(vec) => vec.as_ptr() as _,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      SharedBackend::MmapMut { buf: mmap, .. } => unsafe { (**mmap).as_ptr() as _ },
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      SharedBackend::Mmap { buf: mmap, .. } => unsafe { (**mmap).as_ptr() as _ },
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      SharedBackend::AnonymousMmap(mmap) => mmap.as_ptr() as _,
    }
  }

  #[inline]
  pub(super) fn header_mut_ptr(&self) -> *mut Header {
    match &self.backend {
      SharedBackend::Vec(vec) => vec.as_ptr() as _,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      SharedBackend::MmapMut { buf: mmap, .. } => unsafe { (**mmap).as_ptr() as _ },
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      SharedBackend::Mmap { buf: mmap, .. } => unsafe { (**mmap).as_ptr() as _ },
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      SharedBackend::AnonymousMmap(mmap) => mmap.as_ptr() as _,
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
  pub(super) unsafe fn unmount(&mut self) {
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    match &self.backend {
      SharedBackend::MmapMut {
        buf,
        file,
        lock,
        shrink_on_drop,
      } => {
        use fs4::FileExt;

        // Any errors during unmapping/closing are ignored as the only way
        // to report them would be through panicking which is highly discouraged
        // in Drop impls, c.f. https://github.com/rust-lang/lang-team/issues/97
        let mmap = &mut **buf;
        let _ = mmap.flush();

        // we must trigger the drop of the mmap
        let _ = Box::from_raw(*buf);

        if *shrink_on_drop {
          let used = self
            .header_ptr()
            .cast::<Header>()
            .as_ref()
            .unwrap()
            .allocated
            .load(Ordering::Acquire);
          if used < self.cap as u64 {
            let _ = file.set_len(used);
          }
        }

        if *lock {
          let _ = file.unlock();
        }
      }
      SharedBackend::Mmap {
        lock,
        file,
        shrink_on_drop,
        buf,
      } => {
        use fs4::FileExt;

        // Any errors during unmapping/closing are ignored as the only way
        // to report them would be through panicking which is highly discouraged
        // in Drop impls, c.f. https://github.com/rust-lang/lang-team/issues/97

        // we must trigger the drop of the mmap before truncating the file
        let _ = Box::from_raw(*buf);

        if *shrink_on_drop {
          let used = self
            .header_ptr()
            .cast::<Header>()
            .as_ref()
            .unwrap()
            .allocated
            .load(Ordering::Acquire);
          if used < self.cap as u64 {
            let _ = file.set_len(used);
          }
        }

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
