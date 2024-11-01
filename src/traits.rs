use among::Among;
use core::{
  ops::{Bound, RangeBounds},
  ptr::NonNull,
  sync::atomic::Ordering,
};
use dbutils::buffer::VacantBuffer;
use either::Either;
use rarena_allocator::Allocator as ArenaAllocator;

use super::{
  allocator::{Allocator, AllocatorExt, Header, Link, NodePointer, Sealed as AllocatorSealed},
  base::{EntryRef, SkipList, VersionedEntryRef},
  iter::Iter,
  Error, Height, KeyBuilder, Options, ValueBuilder, MIN_VERSION,
};

/// [`Map`](map::Map) implementation
pub mod map;

/// [`Map`](multiple_version::Map) implementation
pub mod multiple_version;

/// The underlying skip list for skip maps
pub trait List<K: ?Sized + 'static, V: ?Sized + 'static>:
  Sized + From<SkipList<K, V, <Self as List<K, V>>::Allocator>>
{
  type Allocator: Allocator;

  fn as_ref(&self) -> &SkipList<K, V, Self::Allocator>;

  fn as_mut(&mut self) -> &mut SkipList<K, V, Self::Allocator>;

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
    exist: bool,
  ) -> Result<Self, Error> {
    use std::boxed::Box;

    let arena = <Self::Allocator as AllocatorSealed>::new(arena, opts);
    let opts = arena.options();
    let max_height: u8 = opts.max_height().into();
    let data_offset = arena.check_capacity(max_height)?;
    if arena.read_only() || exist {
      let (meta, head, tail) = arena.get_pointers();

      return Ok(Self::from(SkipList::construct(
        arena,
        meta,
        head,
        tail,
        data_offset,
      )));
    }

    let meta = if AllocatorSealed::unify(&arena) {
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
    )))
  }
}

/// The wrapper trait over a underlying [`Allocator`](rarena_allocator::Allocator).
pub trait Arena<K: ?Sized + 'static, V: ?Sized + 'static>: List<K, V> {
  /// Returns how many bytes are reserved by the ARENA.
  #[inline]
  fn reserved_bytes(&self) -> usize {
    self.as_ref().arena.reserved_bytes()
  }

  /// Returns the reserved bytes of the allocator specified in the [`Options::with_reserved`].
  #[inline]
  fn reserved_slice(&self) -> &[u8] {
    self.as_ref().arena.reserved_slice()
  }

  /// Returns the mutable reserved bytes of the allocator specified in the [`Options::with_reserved`].
  ///
  /// ## Safety
  /// - The caller need to make sure there is no data-race
  ///
  /// # Panics
  /// - If in read-only mode, it will panic.
  #[allow(clippy::mut_from_ref)]
  #[inline]
  unsafe fn reserved_slice_mut(&self) -> &mut [u8] {
    self.as_ref().arena.reserved_slice_mut()
  }

  /// Returns the path of the mmap file, only returns `Some` when the ARENA is backed by a mmap file.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn path(
    &self,
  ) -> Option<&<<Self::Allocator as AllocatorSealed>::Allocator as ArenaAllocator>::Path> {
    self.as_ref().arena.path()
  }

  /// Sets remove on drop, only works on mmap with a file backend.
  ///
  /// Default is `false`.
  ///
  /// > **WARNING:** Once set to `true`, the backed file will be removed when the allocator is dropped, even though the file is opened in
  /// > read-only mode.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn remove_on_drop(&self, val: bool) {
    self.as_ref().arena.remove_on_drop(val)
  }

  /// Returns the offset of the data section in the `SkipMap`.
  ///
  /// By default, `SkipMap` will allocate meta, head node, and tail node in the ARENA,
  /// and the data section will be allocated after the tail node.
  ///
  /// This method will return the offset of the data section in the ARENA.
  #[inline]
  fn data_offset(&self) -> usize {
    self.as_ref().data_offset()
  }

  /// Returns the magic version number of the [`Arena`].
  ///
  /// This value can be used to check the compatibility for application using [`Arena`].
  #[inline]
  fn magic_version(&self) -> u16 {
    self.as_ref().magic_version()
  }

  /// Returns the height of the highest tower within any of the nodes that
  /// have ever been allocated as part of this skiplist.
  #[inline]
  fn height(&self) -> u8 {
    self.as_ref().height()
  }

  /// Returns the number of remaining bytes can be allocated by the arena.
  #[inline]
  fn remaining(&self) -> usize {
    self.as_ref().remaining()
  }

  /// Returns the number of bytes that have allocated from the arena.
  #[inline]
  fn allocated(&self) -> usize {
    self.as_ref().allocated()
  }

  /// Returns the capacity of the arena.
  #[inline]
  fn capacity(&self) -> usize {
    self.as_ref().capacity()
  }

  /// Returns the number of entries in the skipmap.
  #[inline]
  fn len(&self) -> usize {
    self.as_ref().len()
  }

  /// Returns true if the skipmap is empty.
  #[inline]
  fn is_empty(&self) -> bool {
    self.len() == 0
  }

  /// Gets the number of pointers to this `SkipMap` similar to [`Arc::strong_count`](std::sync::Arc::strong_count).
  #[inline]
  fn refs(&self) -> usize {
    self.as_ref().refs()
  }

  /// Returns how many bytes are discarded by the ARENA.
  #[inline]
  fn discarded(&self) -> u32 {
    self.as_ref().discarded()
  }

  /// Returns `true` if the Arena is using unify memory layout.
  #[inline]
  fn unify(&self) -> bool {
    self.as_ref().arena.unify()
  }

  /// Returns a random generated height.
  ///
  /// This method is useful when you want to check if the underlying allocator can allocate a node.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{map::sync::SkipMap, Arena, Options};
  ///
  /// let map = Options::new().with_capacity(1024).alloc::<_, _, SkipMap<[u8], [u8]>>().unwrap();
  /// let height = map.random_height();
  ///
  /// let needed = SkipMap::<[u8], [u8]>::estimated_node_size(height, b"k1".len(), b"k2".len());
  /// ```
  #[inline]
  fn random_height(&self) -> Height {
    self.as_ref().random_height()
  }

  /// Returns the estimated size of a node with the given height and key/value sizes.
  ///
  /// **Note**: The returned size is only an estimate and may not be accurate, which means that the actual size is less than or equal to the returned size.
  #[inline]
  fn estimated_node_size(height: Height, key_size: usize, value_size: usize) -> usize {
    SkipList::<K, V, Self::Allocator>::estimated_node_size(height, key_size, value_size)
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
  /// let map = Options::new().with_capacity(100).alloc().unwrap();
  ///
  /// map.insert(b"hello", b"world").unwrap();
  ///
  /// let data = map.get(b"hello").unwrap();
  ///
  /// map.clear().unwrap();
  ///
  /// let w = data[0]; // undefined behavior
  /// ```
  #[inline]
  unsafe fn clear(&mut self) -> Result<(), Error> {
    self.as_mut().clear()
  }

  /// Flushes outstanding memory map modifications to disk.
  ///
  /// When this method returns with a non-error result,
  /// all outstanding changes to a file-backed memory map are guaranteed to be durably stored.
  /// The file's metadata (including last modification timestamp) may not be updated.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn flush(&self) -> std::io::Result<()> {
    self.as_ref().arena.flush()
  }

  /// Asynchronously flushes outstanding memory map modifications to disk.
  ///
  /// This method initiates flushing modified pages to durable storage, but it will not wait for
  /// the operation to complete before returning. The file's metadata (including last
  /// modification timestamp) may not be updated.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn flush_async(&self) -> std::io::Result<()> {
    self.as_ref().arena.flush_async()
  }
}

impl<K: ?Sized + 'static, V: ?Sized + 'static, T> Arena<K, V> for T where T: List<K, V> {}
