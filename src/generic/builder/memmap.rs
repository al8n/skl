use core::mem;

use either::Either;

use super::Builder;
use crate::{
  allocator::{Node, Sealed},
  error::{bad_magic_version, bad_version, flags_mismtach, invalid_data},
  options::CURRENT_VERSION,
  traits::Constructable,
  Arena,
};

impl<C> Builder<C> {
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
  /// use skl::generic::{unique::sync, multiple_version::unsync, Builder, DefaultComparator};
  ///
  /// let map = Builder::<DefaultComparator<[u8]>>::new().with_capacity(1024).map_anon::<sync::SkipMap<[u8], [u8]>>().unwrap();
  ///
  /// let arena = Builder::<DefaultComparator<[u8]>>::new().with_capacity(1024).map_anon::<unsync::SkipMap<[u8], [u8]>>().unwrap();
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
    let Self { options, cmp, .. } = self;

    options
      .to_arena_options()
      .with_maximum_alignment(node_align)
      .map_anon::<<<T::Constructable as Constructable>::Allocator as Sealed>::Allocator>()
      .map_err(Into::into)
      .and_then(|arena| T::construct(arena, options, false, cmp).map_err(invalid_data))
  }

  /// Opens a read-only map which backed by file-backed memory map.
  ///
  /// ## Safety
  /// - All file-backed memory map constructors are marked `unsafe` because of the potential for
  ///   *Undefined Behavior* (UB) using the map if the underlying file is subsequently modified, in or
  ///   out of process. Applications must consider the risk and take appropriate precautions when
  ///   using file-backed maps. Solutions such as file permissions, locks or process-private (e.g.
  ///   unlinked) files exist but are platform specific and limited.
  /// - The `K` and `V` types must be the same as the types used to create the map.
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
  /// - All file-backed memory map constructors are marked `unsafe` because of the potential for
  ///   *Undefined Behavior* (UB) using the map if the underlying file is subsequently modified, in or
  ///   out of process. Applications must consider the risk and take appropriate precautions when
  ///   using file-backed maps. Solutions such as file permissions, locks or process-private (e.g.
  ///   unlinked) files exist but are platform specific and limited.
  /// - The `K` and `V` types must be the same as the types used to create the map.
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
    use crate::allocator::Meta as _;

    let node_align =
      mem::align_of::<<<T::Constructable as Constructable>::Allocator as Sealed>::Node>();

    let Self { options, cmp, .. } = self;
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
            let flags = map.meta().flags();
            let node_flags = <<<T::Constructable as Constructable>::Allocator as Sealed>::Node as Node>::flags();

            if flags != node_flags {
              return Err(flags_mismtach(flags, node_flags));
            }

            if Arena::magic_version(&map) != magic_version {
              Err(bad_magic_version())
            } else if map.as_ref().version() != CURRENT_VERSION {
              Err(bad_version())
            } else {
              Ok(map)
            }
          })
          .map_err(Either::Right)
      })
  }

  /// Creates a new map or reopens a map which backed by a file backed memory map.
  ///
  /// ## Safety
  ///
  /// - All file-backed memory map constructors are marked `unsafe` because of the potential for
  ///   *Undefined Behavior* (UB) using the map if the underlying file is subsequently modified, in or
  ///   out of process. Applications must consider the risk and take appropriate precautions when
  ///   using file-backed maps. Solutions such as file permissions, locks or process-private (e.g.
  ///   unlinked) files exist but are platform specific and limited.
  /// - The `K` and `V` types must be the same as the types used to create the map.
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
  /// - All file-backed memory map constructors are marked `unsafe` because of the potential for
  ///   *Undefined Behavior* (UB) using the map if the underlying file is subsequently modified, in or
  ///   out of process. Applications must consider the risk and take appropriate precautions when
  ///   using file-backed maps. Solutions such as file permissions, locks or process-private (e.g.
  ///   unlinked) files exist but are platform specific and limited.
  /// - The `K` and `V` types must be the same as the types used to create the map.
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
    use crate::allocator::Meta as _;

    let node_align =
      mem::align_of::<<<T::Constructable as Constructable>::Allocator as Sealed>::Node>();
    let Self { options, cmp, .. } = self;
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
            let flags = map.meta().flags();
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
              Ok(map)
            }
          })
          .map_err(Either::Right)
      })
  }
}
