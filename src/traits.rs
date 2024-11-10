use core::{mem, ptr::NonNull, sync::atomic::Ordering};
use rarena_allocator::Allocator as ArenaAllocator;

use crate::Header;

use super::{
  allocator::{Allocator, AllocatorExt, Link, Meta, Node, NodePointer, Sealed as AllocatorSealed},
  error::Error,
  options::Options,
  types::Height,
};

pub trait Constructable: Sized {
  type Allocator: Allocator;
  type Comparator;

  fn allocator(&self) -> &Self::Allocator;

  fn allocator_mut(&mut self) -> &mut Self::Allocator;

  fn magic_version(&self) -> u16;

  #[inline]
  fn version(&self) -> u16 {
    ArenaAllocator::magic_version(self.allocator().arena())
  }

  fn len(&self) -> usize;

  fn height(&self) -> u8;

  fn random_height(&self) -> Height;

  fn header(&self) -> Option<&Header>;

  fn construct(
    arena: Self::Allocator,
    meta: NonNull<<Self::Allocator as AllocatorSealed>::Meta>,
    head: <<Self::Allocator as AllocatorSealed>::Node as Node>::Pointer,
    tail: <<Self::Allocator as AllocatorSealed>::Node as Node>::Pointer,
    header: Option<Header>,
    cmp: Self::Comparator,
  ) -> Self;
}

/// The underlying skip list for skip maps
pub trait List: Sized + From<Self::Constructable> {
  type Constructable: Constructable;

  fn as_ref(&self) -> &Self::Constructable;

  fn as_mut(&mut self) -> &mut Self::Constructable;

  fn meta(&self) -> &<<Self::Constructable as Constructable>::Allocator as AllocatorSealed>::Meta;

  fn construct(
    arena: <<Self::Constructable as Constructable>::Allocator as AllocatorSealed>::Allocator,
    opts: Options,
    exist: bool,
    cmp: <Self::Constructable as Constructable>::Comparator,
  ) -> Result<Self, Error> {
    use std::boxed::Box;

    let arena =
      <<Self::Constructable as Constructable>::Allocator as AllocatorSealed>::new(arena, opts);
    let opts = arena.options();
    let max_height: u8 = opts.max_height().into();
    if arena.read_only() || exist {
      let header = arena.calculate_header(max_height)?;
      let (meta, head, tail) = arena.get_pointers(header);

      return Ok(Self::from(
        <Self::Constructable as Constructable>::construct(
          arena,
          meta,
          head,
          tail,
          Some(header),
          cmp,
        ),
      ));
    }

    let (header_offset, meta) = if AllocatorSealed::unify(&arena) {
      arena
        .allocate_header(opts.magic_version())
        .map(|(header_offset, meta)| (Some(header_offset as u32), meta))?
    } else {
      unsafe {
        (None, NonNull::new_unchecked(Box::into_raw(Box::new(
          <<<Self::Constructable as Constructable>::Allocator as AllocatorSealed>::Meta as Meta>::new(opts.magic_version()),
        ))))
      }
    };

    let head = arena.allocate_full_node(max_height)?;
    let tail = arena.allocate_full_node(max_height)?;

    let head_offset = head.offset();
    let tail_offset = tail.offset();

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

    let header =
      header_offset.map(|meta_offset| Header::new(meta_offset, head_offset, tail_offset));

    Ok(Self::from(
      <Self::Constructable as Constructable>::construct(arena, meta, head, tail, header, cmp),
    ))
  }

  /// ## Safety
  /// - The `data_offset` must be the same as the same as
  unsafe fn try_open_from_allocator<L: List>(
    arena: <L::Constructable as Constructable>::Allocator,
    cmp: <L::Constructable as Constructable>::Comparator,
    header: Header,
  ) -> Result<L, Error> {
    let (meta, head, tail) = arena.get_pointers(header);

    Ok(L::from(<L::Constructable as Constructable>::construct(
      arena,
      meta,
      head,
      tail,
      Some(header),
      cmp,
    )))
  }

  /// ## Safety
  /// - If the ARENA is file-backed, the caller must save the `data_offset` of the `SkipMap` before the ARENA is closed,
  ///   so that users can reopen the `SkipMap` with the same `data_offset`.
  unsafe fn try_create_from_allocator<L: List>(
    arena: <L::Constructable as Constructable>::Allocator,
    cmp: <L::Constructable as Constructable>::Comparator,
  ) -> Result<L, Error> {
    use std::boxed::Box;

    let opts = arena.options();
    let max_height: u8 = opts.max_height().into();
    if arena.read_only() {
      return Err(Error::read_only());
    }

    let (header_offset, meta) = if AllocatorSealed::unify(&arena) {
      arena
        .allocate_header(opts.magic_version())
        .map(|(header_offset, meta)| (Some(header_offset as u32), meta))?
    } else {
      unsafe {
        (None, NonNull::new_unchecked(Box::into_raw(Box::new(
          <<<L::Constructable as Constructable>::Allocator as AllocatorSealed>::Meta as Meta>::new(opts.magic_version()),
        ))))
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
    let head_offset = head.offset();
    let tail_offset = tail.offset();

    Ok(L::from(<L::Constructable as Constructable>::construct(
      arena,
      meta,
      head,
      tail,
      header_offset.map(|offset| Header::new(offset, head_offset, tail_offset)),
      cmp,
    )))
  }
}

/// The wrapper trait over a underlying [`Allocator`](rarena_allocator::Allocator).
pub trait Arena: List {
  /// Returns how many bytes are reserved by the ARENA.
  #[inline]
  fn reserved_bytes(&self) -> usize {
    self.as_ref().allocator().reserved_bytes()
  }

  /// Returns the reserved bytes of the allocator specified in the [`Options::with_reserved`].
  #[inline]
  fn reserved_slice(&self) -> &[u8] {
    self.as_ref().allocator().reserved_slice()
  }

  /// Clear the allocator to empty and re-initialize.
  ///
  /// ## Safety
  /// - The current pointers get from the allocator cannot be used anymore after calling this method.
  /// - This method is not thread-safe.
  /// - This will clear the whole ARENA, all `SkipMap`s based on this ARENA cannot be used anymore after calling this method.
  ///
  /// ## Example
  ///
  /// Undefine behavior:
  ///
  /// ```ignore
  /// let mut map = Builder::new().with_capacity(100).alloc().unwrap();
  ///
  /// map.insert(b"hello", b"world").unwrap();
  ///
  /// let data = map.get(b"hello").unwrap();
  ///
  /// map.allocator_mut().clear().unwrap();
  ///
  /// let w = data[0]; // undefined behavior
  /// ```
  unsafe fn clear(&mut self) -> Result<(), Error> {
    self.allocator_mut().clear().map_err(Into::into)
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
    self.as_ref().allocator().reserved_slice_mut()
  }

  /// Returns the path of the mmap file, only returns `Some` when the ARENA is backed by a mmap file.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn path(
    &self,
  ) -> Option<&<<<Self::Constructable as Constructable>::Allocator as AllocatorSealed>::Allocator as ArenaAllocator>::Path>{
    self.as_ref().allocator().path()
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
    self.as_ref().allocator().remove_on_drop(val)
  }

  /// Returns the magic version number of the [`Arena`].
  ///
  /// This value can be used to check the compatibility for application using [`Arena`].
  #[inline]
  fn magic_version(&self) -> u16 {
    self.as_ref().magic_version()
  }

  /// Returns the number of bytes that have allocated from the arena.
  #[inline]
  fn allocated(&self) -> usize {
    self.as_ref().allocator().allocated()
  }

  /// Returns the capacity of the arena.
  #[inline]
  fn capacity(&self) -> usize {
    self.as_ref().allocator().capacity()
  }

  /// Returns the number of remaining bytes can be allocated by the arena.
  #[inline]
  fn remaining(&self) -> usize {
    self.as_ref().allocator().remaining()
  }

  /// Gets the number of pointers to this `SkipMap` similar to [`Arc::strong_count`](std::sync::Arc::strong_count).
  #[inline]
  fn refs(&self) -> usize {
    self.as_ref().allocator().refs()
  }

  /// Returns how many bytes are discarded by the ARENA.
  #[inline]
  fn discarded(&self) -> u32 {
    self.as_ref().allocator().discarded()
  }

  /// Returns `true` if the Arena is using unify memory layout.
  #[inline]
  fn unify(&self) -> bool {
    self.as_ref().allocator().unify()
  }

  /// Returns the allocator used to allocate nodes.
  #[inline]
  fn allocator(&self) -> &<Self::Constructable as Constructable>::Allocator {
    self.as_ref().allocator()
  }

  /// Returns the mutable reference to the allocator used to allocate nodes.
  #[inline]
  fn allocator_mut(&mut self) -> &mut <Self::Constructable as Constructable>::Allocator {
    self.as_mut().allocator_mut()
  }

  /// Returns the estimated size of a node with the given height and key/value sizes.
  ///
  /// **Note**: The returned size is only an estimate and may not be accurate, which means that the actual size is less than or equal to the returned size.
  #[inline]
  fn estimated_node_size(height: Height, key_size: usize, value_size: usize) -> usize {
    let height: usize = height.into();
    7 // max padding
      + mem::size_of::<<<Self::Constructable as Constructable>::Allocator as AllocatorSealed>::Node>()
      + mem::size_of::<<<<Self::Constructable as Constructable>::Allocator as AllocatorSealed>::Node as Node>::Link>() * height
      + key_size
      + value_size
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
    self.as_ref().allocator().flush()
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
    self.as_ref().allocator().flush_async()
  }
}

impl<T> Arena for T where T: List {}
