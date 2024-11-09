use core::mem;

use dbutils::equivalentor::Comparator;
use either::Either;
use rarena_allocator::Allocator;

use super::Builder;
use crate::{
  allocator::{Node, Sealed},
  error::{bad_magic_version, bad_version, flags_mismtach, invalid_data},
  options::CURRENT_VERSION,
  traits::Constructable,
  Arena,
};

impl<C: Comparator> Builder<C> {
  /// Create a new map which is backed by a anonymous memory map.
  ///
  /// **What the difference between this method and [`Builder::alloc`]?**
  ///
  /// 1. This method will use mmap anonymous to require memory from the OS directly.
  ///    If you require very large contiguous memory regions, this method might be more suitable because
  ///    it's more direct in requesting large chunks of memory from the OS.
  ///
  /// 2. Where as [`Builder::alloc`] will use an `AlignedVec` ensures we are working within Rust's memory safety guarantees.
  ///    Even if we are working with raw pointers with `Box::into_raw`,
  ///    the backend ARENA will reclaim the ownership of this memory by converting it back to a `Box`
  ///    when dropping the backend ARENA. Since `AlignedVec` uses heap memory, the data might be more cache-friendly,
  ///    especially if you're frequently accessing or modifying it.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::dynamic::{unique::sync, multiple_version::unsync, Builder};
  ///
  /// let map = Builder::new().with_capacity(1024).map_anon::<sync::SkipMap>().unwrap();
  ///
  /// let arena = Builder::new().with_capacity(1024).map_anon::<unsync::SkipMap>().unwrap();
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub fn map_anon<T>(self) -> std::io::Result<T>
  where
    T: Arena,
    T::Constructable: Constructable<Comparator = C>,
  {
    let node_align =
      mem::align_of::<<<T::Constructable as Constructable>::Allocator as Sealed>::Node>();
    let Builder { options, cmp } = self;

    #[allow(clippy::bind_instead_of_map)]
    options
      .to_arena_options()
      .with_maximum_alignment(node_align)
      .map_anon::<<<T::Constructable as Constructable>::Allocator as Sealed>::Allocator>()
      .map_err(Into::into)
      .and_then(|arena| {
        T::construct(arena, options, false, cmp)
          .map_err(invalid_data)
          .and_then(|map| {
            // Lock the memory of first page to prevent it from being swapped out.
            #[cfg(not(miri))]
            if options.lock_meta {
              unsafe {
                let arena = map.as_ref().allocator();
                arena.mlock(0, arena.page_size().min(arena.capacity()))?;
              }
            }

            Ok(map)
          })
      })
  }

  /// Opens a read-only map which backed by file-backed memory map.
  ///
  /// ## Safety
  /// - The file must be created with the same [`Comparator`].
  /// - All file-backed memory map constructors are marked `unsafe` because of the potential for
  ///   *Undefined Behavior* (UB) using the map if the underlying file is subsequently modified, in or
  ///   out of process. Applications must consider the risk and take appropriate precautions when
  ///   using file-backed maps. Solutions such as file permissions, locks or process-private (e.g.
  ///   unlinked) files exist but are platform specific and limited.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub unsafe fn map<T, P>(self, path: P) -> std::io::Result<T>
  where
    T: Arena,
    T::Constructable: Constructable<Comparator = C>,
    P: AsRef<std::path::Path>,
  {
    self
      .map_with_path_builder::<T, _, ()>(|| Ok(path.as_ref().to_path_buf()))
      .map_err(Either::unwrap_right)
  }

  /// Opens a read-only map which backed by file-backed memory map with a path builder.
  ///
  /// ## Safety
  /// - The file must be created with the same [`Comparator`].
  /// - All file-backed memory map constructors are marked `unsafe` because of the potential for
  ///   *Undefined Behavior* (UB) using the map if the underlying file is subsequently modified, in or
  ///   out of process. Applications must consider the risk and take appropriate precautions when
  ///   using file-backed maps. Solutions such as file permissions, locks or process-private (e.g.
  ///   unlinked) files exist but are platform specific and limited.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub unsafe fn map_with_path_builder<T, PB, E>(
    self,
    path_builder: PB,
  ) -> Result<T, Either<E, std::io::Error>>
  where
    T: Arena,
    T::Constructable: Constructable<Comparator = C>,
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    let node_align =
      mem::align_of::<<<T::Constructable as Constructable>::Allocator as Sealed>::Node>();

    let Self { options, cmp } = self;
    let magic_version = options.magic_version();

    #[allow(clippy::bind_instead_of_map)]
    options
      .to_arena_options()
      .with_unify(true)
      .with_read(true)
      .with_create(false)
      .with_create_new(false)
      .with_write(false)
      .with_truncate(false)
      .with_append(false)
      .with_maximum_alignment(node_align)
      .map_with_path_builder::<<<T::Constructable as Constructable>::Allocator as Sealed>::Allocator, _, _>(path_builder)
      .and_then(|arena| {
        T::construct(arena, options, true, cmp)
          .map_err(invalid_data)
          .and_then(|map| {
            let flags = map.flags();
            let node_flags = <<<T::Constructable as Constructable>::Allocator as Sealed>::Node as Node>::flags();

            if flags != node_flags {
              return Err(flags_mismtach(flags, node_flags));
            }

            if Arena::magic_version(&map) != magic_version {
              Err(bad_magic_version())
            } else if map.as_ref().version() != CURRENT_VERSION {
              Err(bad_version())
            } else {
              // Lock the memory of first page to prevent it from being swapped out.
              #[cfg(not(miri))]
              if options.lock_meta {
                unsafe {
                  let allocator = map.as_ref().allocator();
                  allocator.mlock(0, allocator.page_size().min(allocator.capacity()))?;
                }
              }

              Ok(map)
            }
          })
          .map_err(Either::Right)
      })
  }

  /// Creates a new map or reopens a map which backed by a file backed memory map.
  ///
  /// ## Safety
  /// - If you are reopening a file, then the file must be created with the same [`Comparator`].
  /// - All file-backed memory map constructors are marked `unsafe` because of the potential for
  ///   *Undefined Behavior* (UB) using the map if the underlying file is subsequently modified, in or
  ///   out of process. Applications must consider the risk and take appropriate precautions when
  ///   using file-backed maps. Solutions such as file permissions, locks or process-private (e.g.
  ///   unlinked) files exist but are platform specific and limited.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub unsafe fn map_mut<T, P>(self, path: P) -> std::io::Result<T>
  where
    T: Arena,
    T::Constructable: Constructable<Comparator = C>,
    P: AsRef<std::path::Path>,
  {
    self
      .map_mut_with_path_builder::<T, _, ()>(|| Ok(path.as_ref().to_path_buf()))
      .map_err(Either::unwrap_right)
  }

  /// Creates a new map or reopens a map which backed by a file backed memory map with path builder.
  ///
  /// # Safety
  /// - If you are reopening a file, then the file must be created with the same [`Comparator`].
  /// - All file-backed memory map constructors are marked `unsafe` because of the potential for
  ///   *Undefined Behavior* (UB) using the map if the underlying file is subsequently modified, in or
  ///   out of process. Applications must consider the risk and take appropriate precautions when
  ///   using file-backed maps. Solutions such as file permissions, locks or process-private (e.g.
  ///   unlinked) files exist but are platform specific and limited.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub unsafe fn map_mut_with_path_builder<T, PB, E>(
    self,
    path_builder: PB,
  ) -> Result<T, Either<E, std::io::Error>>
  where
    T: Arena,
    T::Constructable: Constructable<Comparator = C>,
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    let node_align =
      mem::align_of::<<<T::Constructable as Constructable>::Allocator as Sealed>::Node>();
    let Self { options, cmp } = self;
    let magic_version = options.magic_version();
    let path = path_builder().map_err(Either::Left)?;
    let exist = path.exists();

    #[allow(clippy::bind_instead_of_map)]
    options
      .to_arena_options()
      .with_maximum_alignment(node_align)
      .with_unify(true)
      .map_mut::<<<T::Constructable as Constructable>::Allocator as Sealed>::Allocator, _>(path)
      .map_err(Either::Right)
      .and_then(|arena| {
        T::construct(arena, options, exist, cmp)
          .map_err(invalid_data)
          .and_then(|map| {
            let flags = map.flags();
            let node_flags =
              <<<T::Constructable as Constructable>::Allocator as Sealed>::Node as Node>::flags();

            if flags != node_flags {
              return Err(flags_mismtach(flags, node_flags));
            }

            if Arena::magic_version(&map) != magic_version {
              Err(bad_magic_version())
            } else if map.as_ref().version() != CURRENT_VERSION {
              Err(bad_version())
            } else {
              // Lock the memory of first page to prevent it from being swapped out.
              #[cfg(not(miri))]
              if options.lock_meta {
                unsafe {
                  let allocator = map.as_ref().allocator();
                  allocator.mlock(0, allocator.page_size().min(allocator.capacity()))?;
                }
              }

              Ok(map)
            }
          })
          .map_err(Either::Right)
      })
  }
}
