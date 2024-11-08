use core::mem;

use super::super::Options;
use crate::{allocator::Sealed, error::Error, traits::Constructable, Arena};

// #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
// #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
// mod memmap;

/// A builder for creating a generic key-value `SkipMap`.
#[derive(Debug, Clone)]
pub struct Builder(Options);

impl Builder {
  /// Create a new map which is backed by a `AlignedVec`.
  ///
  /// **Note:** The capacity stands for how many memory allocated,
  /// it does not mean the skiplist can store `cap` entries.
  ///
  /// **What the difference between this method and [`Options::map_anon`]?**
  ///
  /// 1. This method will use an `AlignedVec` ensures we are working within Rust's memory safety guarantees.
  ///    Even if we are working with raw pointers with `Box::into_raw`,
  ///    the backend ARENA will reclaim the ownership of this memory by converting it back to a `Box`
  ///    when dropping the backend ARENA. Since `AlignedVec` uses heap memory, the data might be more cache-friendly,
  ///    especially if you're frequently accessing or modifying it.
  ///
  /// 2. Where as [`Options::map_anon`] will use mmap anonymous to require memory from the OS.
  ///    If you require very large contiguous memory regions, `mmap` might be more suitable because
  ///    it's more direct in requesting large chunks of memory from the OS.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{map::sync, multiple_version::unsync, Options};
  ///
  /// let map = Options::new().with_capacity(1024).alloc::<_, _, sync::SkipMap<[u8], [u8]>>().unwrap();
  ///
  /// let arena = Options::new().with_capacity(1024).alloc::<_, _, unsync::SkipMap<[u8], [u8]>>().unwrap();
  /// ```
  #[inline]
  pub fn alloc<T>(self) -> Result<T, Error>
  where
    T: Arena,
    T::Constructable: Constructable<Comparator = ()>,
  {
    let node_align =
      mem::align_of::<<<T::Constructable as Constructable>::Allocator as Sealed>::Node>();

    let Builder(options) = self;
    options
      .to_arena_options()
      .with_maximum_alignment(node_align)
      .alloc::<<<T::Constructable as Constructable>::Allocator as Sealed>::Allocator>()
      .map_err(Into::into)
      .and_then(|arena| T::construct(arena, options, false, ()))
  }
}
