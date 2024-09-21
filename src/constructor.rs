use among::Among;
use core::{
  borrow::Borrow,
  ops::{Bound, RangeBounds},
  ptr::NonNull,
  sync::atomic::Ordering,
};
use dbutils::{buffer::VacantBuffer, Comparator};
use either::Either;
use rarena_allocator::Allocator as ArenaAllocator;

use super::{
  allocator::{
    Allocator, AllocatorExt, Header, Link, NodePointer, Sealed as AllocatorSealed, WithTrailer,
  },
  base::SkipList,
  EntryRef, Error, Height, Iter, KeyBuilder, Options, ValueBuilder, MIN_VERSION,
};

mod container;
pub use container::*;

/// [`TrailedMap`](trailed::TrailedMap) implementation
pub mod trailed;

/// [`Map`](map::Map) implementation
pub mod map;

/// The underlying skip list for skip maps
pub trait List:
  Sized + From<SkipList<<Self as List>::Allocator, <Self as List>::Comparator>>
{
  type Allocator: Allocator;
  type Comparator;

  fn as_ref(&self) -> &SkipList<Self::Allocator, Self::Comparator>;

  fn as_mut(&mut self) -> &mut SkipList<Self::Allocator, Self::Comparator>;

  #[inline]
  fn allocator(&self) -> &Self::Allocator {
    &self.as_ref().arena
  }

  #[inline]
  fn magic_version(&self) -> u16 {
    self.as_ref().magic_version()
  }

  #[inline]
  fn version(&self) -> u16 {
    ArenaAllocator::magic_version(core::ops::Deref::deref(&self.as_ref().arena))
  }

  fn construct(
    arena: <Self::Allocator as AllocatorSealed>::Allocator,
    opts: Options,
    cmp: Self::Comparator,
  ) -> Result<Self, Error> {
    use std::boxed::Box;

    let arena = <Self::Allocator as AllocatorSealed>::new(arena, opts);

    let opts = arena.options();
    let max_height: u8 = opts.max_height().into();
    let data_offset = arena.check_capacity(max_height)?;
    if arena.read_only() {
      let (meta, head, tail) = arena.get_pointers();

      return Ok(Self::from(SkipList::construct(
        arena,
        meta,
        head,
        tail,
        data_offset,
        cmp,
      )));
    }

    let meta = if opts.unify() {
      arena.allocate_header(opts.magic_version())?
    } else {
      unsafe {
        NonNull::new_unchecked(Box::into_raw(Box::new(
          <<Self::Allocator as AllocatorSealed>::Header as Header>::new(opts.magic_version()),
        )))
      }
    };

    let head = arena.allocate_full_node(max_height)?;
    let tail = arena.allocate_full_node(max_height)?;

    // Safety:
    // We will always allocate enough space for the head node and the tail node.
    unsafe {
      // Link all head/tail levels together.
      for i in 0..(max_height as usize) {
        let head_link = head.tower(&arena, i);
        let tail_link = tail.tower(&arena, i);
        head_link.store_next_offset(tail.offset(), Ordering::Relaxed);
        tail_link.store_prev_offset(head.offset(), Ordering::Relaxed);
      }
    }

    Ok(Self::from(SkipList::construct(
      arena,
      meta,
      head,
      tail,
      data_offset,
      cmp,
    )))
  }
}

pub trait Arena: List {
  /// Returns the reserved bytes of the allocator specified in the [`ArenaOptions::with_reserved`].
  fn reserved_slice(&self) -> &[u8];

  /// Returns the mutable reserved bytes of the allocator specified in the [`ArenaOptions::with_reserved`].
  ///
  /// ## Safety
  /// - The caller need to make sure there is no data-race
  ///
  /// # Panics
  /// - If in read-only mode, it will panic.
  #[allow(clippy::mut_from_ref)]
  unsafe fn reserved_slice_mut(&self) -> &mut [u8];

  // /// Returns the path of the mmap file, only returns `Some` when the ARENA is backed by a mmap file.
  // #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  // #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  // #[inline]
  // fn path(&self) -> Option<&std::sync::Arc<std::path::PathBuf>> {
  //   self.as_ref().arena.path()
  // }

  /// Sets remove on drop, only works on mmap with a file backend.
  ///
  /// Default is `false`.
  ///
  /// > **WARNING:** Once set to `true`, the backed file will be removed when the allocator is dropped, even though the file is opened in
  /// > read-only mode.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn remove_on_drop(&self, val: bool);

  /// Returns the offset of the data section in the `SkipMap`.
  ///
  /// By default, `SkipMap` will allocate meta, head node, and tail node in the ARENA,
  /// and the data section will be allocated after the tail node.
  ///
  /// This method will return the offset of the data section in the ARENA.
  fn data_offset(&self) -> usize;

  /// Returns the magic version number of the [`SkipMap`].
  ///
  /// This value can be used to check the compatibility for application using [`SkipMap`].
  fn magic_version(&self) -> u16;

  /// Returns the height of the highest tower within any of the nodes that
  /// have ever been allocated as part of this skiplist.
  fn height(&self) -> u8;

  /// Returns the number of remaining bytes can be allocated by the arena.
  fn remaining(&self) -> usize;

  /// Returns the number of bytes that have allocated from the arena.
  fn allocated(&self) -> usize;

  /// Returns the capacity of the arena.
  fn capacity(&self) -> usize;

  /// Returns the number of entries in the skipmap.
  fn len(&self) -> usize;

  /// Returns true if the skipmap is empty.
  fn is_empty(&self) -> bool;

  /// Gets the number of pointers to this `SkipMap` similar to [`Arc::strong_count`](std::sync::Arc::strong_count).
  fn refs(&self) -> usize;

  /// Returns how many bytes are discarded by the ARENA.
  fn discarded(&self) -> u32;

  /// Returns the comparator used to compare keys.
  fn comparator(&self) -> &Self::Comparator;

  /// Returns a random generated height.
  ///
  /// This method is useful when you want to check if the underlying allocator can allocate a node.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{sync::trailed::SkipMap, Options};
  ///
  /// let map = SkipMap::<u64>::new(Options::new()).unwrap();
  /// let height = map.random_height();
  ///
  /// let needed = SkipMap::<u64>::estimated_node_size(height, b"k1".len(), b"k2".len());
  /// ```
  fn random_height(&self) -> Height;

  /// Returns the estimated size of a node with the given height and key/value sizes.
  ///
  /// **Note**: The returned size is only an estimate and may not be accurate, which means that the actual size is less than or equal to the returned size.
  #[inline]
  fn estimated_node_size(height: Height, key_size: usize, value_size: usize) -> usize {
    SkipList::<Self::Allocator, Self::Comparator>::estimated_node_size(height, key_size, value_size)
  }

  /// Clear the skiplist to empty and re-initialize.
  ///
  /// ## Safety
  /// - The current pointers get from the ARENA cannot be used anymore after calling this method.
  /// - This method is not thread-safe.
  ///
  /// ## Example
  ///
  /// Undefine behavior:
  ///
  /// ```ignore
  /// let map = SkipMap::new(Options::new()).unwrap();
  ///
  /// map.insert(b"hello", b"world").unwrap();
  ///
  /// let data = map.get(b"hello").unwrap();
  ///
  /// map.clear().unwrap();
  ///
  /// let w = data[0]; // undefined behavior
  /// ```
  unsafe fn clear(&mut self) -> Result<(), Error>;

  /// Flushes outstanding memory map modifications to disk.
  ///
  /// When this method returns with a non-error result,
  /// all outstanding changes to a file-backed memory map are guaranteed to be durably stored.
  /// The file's metadata (including last modification timestamp) may not be updated.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn flush(&self) -> std::io::Result<()>;

  /// Asynchronously flushes outstanding memory map modifications to disk.
  ///
  /// This method initiates flushing modified pages to durable storage, but it will not wait for
  /// the operation to complete before returning. The file's metadata (including last
  /// modification timestamp) may not be updated.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn flush_async(&self) -> std::io::Result<()>;
}

impl<T> Arena for T
where
  T: List,
{
  #[inline]
  fn reserved_slice(&self) -> &[u8] {
    self.as_ref().arena.reserved_slice()
  }

  #[inline]
  #[allow(clippy::mut_from_ref)]
  unsafe fn reserved_slice_mut(&self) -> &mut [u8] {
    self.as_ref().arena.reserved_slice_mut()
  }

  // /// Returns the path of the mmap file, only returns `Some` when the ARENA is backed by a mmap file.
  // #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  // #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  // #[inline]
  // fn path(&self) -> Option<&std::sync::Arc<std::path::PathBuf>> {
  //   self.as_ref().arena.path()
  // }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn remove_on_drop(&self, val: bool) {
    self.as_ref().remove_on_drop(val);
  }

  #[inline]
  fn data_offset(&self) -> usize {
    self.as_ref().data_offset()
  }

  #[inline]
  fn magic_version(&self) -> u16 {
    self.as_ref().magic_version()
  }

  #[inline]
  fn height(&self) -> u8 {
    self.as_ref().height()
  }

  #[inline]
  fn remaining(&self) -> usize {
    self.as_ref().remaining()
  }

  #[inline]
  fn allocated(&self) -> usize {
    self.as_ref().allocated()
  }

  #[inline]
  fn capacity(&self) -> usize {
    self.as_ref().capacity()
  }

  #[inline]
  fn len(&self) -> usize {
    self.as_ref().len()
  }

  #[inline]
  fn is_empty(&self) -> bool {
    self.as_ref().is_empty()
  }

  #[inline]
  fn refs(&self) -> usize {
    self.as_ref().refs()
  }

  #[inline]
  fn discarded(&self) -> u32 {
    self.as_ref().discarded()
  }

  #[inline]
  fn comparator(&self) -> &<Self as List>::Comparator {
    self.as_ref().comparator()
  }

  #[inline]
  fn random_height(&self) -> Height {
    self.as_ref().random_height()
  }

  unsafe fn clear(&mut self) -> Result<(), Error> {
    self.as_mut().clear()
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn flush(&self) -> std::io::Result<()> {
    self.as_ref().flush()
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn flush_async(&self) -> std::io::Result<()> {
    self.as_ref().flush_async()
  }
}
