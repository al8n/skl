use rarena_allocator::{
  sync::{Arena, BytesRefMut, RefMut},
  ArenaOptions, Error as ArenaError,
};

use core::{
  cmp,
  convert::Infallible,
  marker::PhantomData,
  mem,
  ops::{Bound, RangeBounds},
  ptr::{self, NonNull},
};

use std::boxed::Box;

use crate::{Trailer, VacantBuffer};

use super::{common::*, *};

use super::base::{
  Allocator as BaseAllocator, BytesRefMut as BaseBytesRefMut, Link as BaseLink, Node as BaseNode,
  NodePointer as BaseNodePointer, RefMut as BaseRefMut, *,
};

use either::Either;

/// a
#[derive(Debug)]
#[repr(C)]
pub struct Meta {
  /// The maximum MVCC version of the skiplist. CAS.
  max_version: AtomicU64,
  /// The minimum MVCC version of the skiplist. CAS.
  min_version: AtomicU64,
  len: AtomicU32,
  magic_version: u16,
  /// Current height. 1 <= height <= 31. CAS.
  height: AtomicU8,
  reserved_byte: u8,
}

impl Header for Meta {
  #[inline]
  fn new(version: u16) -> Self {
    Self {
      max_version: AtomicU64::new(0),
      min_version: AtomicU64::new(0),
      magic_version: version,
      height: AtomicU8::new(1),
      len: AtomicU32::new(0),
      reserved_byte: 0,
    }
  }

  #[inline]
  fn magic_version(&self) -> u16 {
    self.magic_version
  }

  #[inline]
  fn max_version(&self) -> u64 {
    self.max_version.load(Ordering::Acquire)
  }

  #[inline]
  fn min_version(&self) -> u64 {
    self.min_version.load(Ordering::Acquire)
  }

  #[inline]
  fn height(&self) -> u8 {
    self.height.load(Ordering::Acquire)
  }

  #[inline]
  fn len(&self) -> u32 {
    self.len.load(Ordering::Acquire)
  }

  #[inline]
  fn increase_len(&self) {
    self.len.fetch_add(1, Ordering::Release);
  }

  fn update_max_version(&self, version: Version) {
    let mut current = self.max_version.load(Ordering::Acquire);
    loop {
      if version <= current {
        return;
      }

      match self.max_version.compare_exchange_weak(
        current,
        version,
        Ordering::SeqCst,
        Ordering::Acquire,
      ) {
        Ok(_) => break,
        Err(v) => current = v,
      }
    }
  }

  fn update_min_version(&self, version: Version) {
    let mut current = self.min_version.load(Ordering::Acquire);
    loop {
      if version >= current {
        return;
      }

      match self.min_version.compare_exchange_weak(
        current,
        version,
        Ordering::SeqCst,
        Ordering::Acquire,
      ) {
        Ok(_) => break,
        Err(v) => current = v,
      }
    }
  }

  #[inline]
  fn compare_exchange_height_weak(
    &self,
    current: u8,
    new: u8,
    success: Ordering,
    failure: Ordering,
  ) -> Result<u8, u8> {
    self
      .height
      .compare_exchange_weak(current, new, success, failure)
  }
}

#[repr(C, align(8))]
pub(crate) struct AtomicValuePointer(AtomicU64);

impl core::fmt::Debug for AtomicValuePointer {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    let (offset, len) = decode_value_pointer(self.0.load(Ordering::Relaxed));
    f.debug_struct("AtomicValuePointer")
      .field("offset", &offset)
      .field("len", &len)
      .finish()
  }
}

impl AtomicValuePointer {
  #[inline]
  fn new(offset: u32, len: u32) -> Self {
    Self(AtomicU64::new(encode_value_pointer(offset, len)))
  }

  #[inline]
  fn load(&self, ordering: Ordering) -> (u32, u32) {
    decode_value_pointer(self.0.load(ordering))
  }

  #[inline]
  fn swap(&self, offset: u32, len: u32) -> (u32, u32) {
    decode_value_pointer(
      self
        .0
        .swap(encode_value_pointer(offset, len), Ordering::AcqRel),
    )
  }

  #[inline]
  fn compare_remove(&self, success: Ordering, failure: Ordering) -> Result<(u32, u32), (u32, u32)> {
    let old = self.0.load(Ordering::Acquire);
    let (offset, _) = decode_value_pointer(old);
    let new = encode_value_pointer(offset, REMOVE);
    self
      .0
      .compare_exchange(old, new, success, failure)
      .map(decode_value_pointer)
      .map_err(decode_value_pointer)
  }
}

impl ValuePointer for AtomicValuePointer {
  const REMOVE: u32 = REMOVE;

  #[inline]
  fn load(&self) -> (u32, u32) {
    decode_value_pointer(AtomicU64::load(&self.0, Ordering::Acquire))
  }

  #[inline]
  fn swap(&self, offset: u32, len: u32) -> (u32, u32) {
    decode_value_pointer(
      self
        .0
        .swap(encode_value_pointer(offset, len), Ordering::AcqRel),
    )
  }
}

#[derive(Debug)]
struct NodePtr<T> {
  ptr: *mut Node<T>,
  offset: u32,
}

impl<T> Clone for NodePtr<T> {
  fn clone(&self) -> Self {
    *self
  }
}

impl<T> Copy for NodePtr<T> {}

impl<T: core::fmt::Debug + Trailer> BaseNodePointer for NodePtr<T> {
  const NULL: Self = Self {
    ptr: ptr::null_mut(),
    offset: 0,
  };

  type Node = Node<T>;

  #[inline]
  fn is_null(&self) -> bool {
    self.offset == 0
  }

  fn offset(&self) -> u32 {
    self.offset
  }

  fn ptr(&self) -> *mut Self::Node {
    self.ptr
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
  unsafe fn next_offset<A: BaseAllocator>(&self, arena: &A, idx: usize) -> u32 {
    self.tower(arena, idx).next_offset.load(Ordering::Acquire)
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
  unsafe fn prev_offset<A: BaseAllocator>(&self, arena: &A, idx: usize) -> u32 {
    self.tower(arena, idx).prev_offset.load(Ordering::Acquire)
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
  unsafe fn cas_prev_offset<A: BaseAllocator>(
    &self,
    arena: &A,
    idx: usize,
    current: u32,
    new: u32,
    success: Ordering,
    failure: Ordering,
  ) -> Result<u32, u32> {
    self
      .tower(arena, idx)
      .prev_offset
      .compare_exchange(current, new, success, failure)
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
  unsafe fn cas_next_offset<A: BaseAllocator>(
    &self,
    arena: &A,
    idx: usize,
    current: u32,
    new: u32,
    success: Ordering,
    failure: Ordering,
  ) -> Result<u32, u32> {
    self
      .tower(arena, idx)
      .next_offset
      .compare_exchange(current, new, success, failure)
  }

  #[inline]
  fn new(ptr: *mut u8, offset: u32) -> Self {
    Self {
      ptr: ptr.cast(),
      offset,
    }
  }

  /// ## Safety
  /// - the pointer must be valid
  #[inline]
  unsafe fn as_ref(&self) -> &Node<T> {
    &*self.ptr.cast()
  }

  /// ## Safety
  /// - the pointer must be valid
  #[inline]
  unsafe fn as_mut(&self) -> &mut Node<T> {
    &mut *self.ptr.cast()
  }
}

#[derive(Debug)]
#[repr(C)]
struct Link {
  next_offset: AtomicU32,
  prev_offset: AtomicU32,
}

impl Link {
  const SIZE: usize = mem::size_of::<Self>();
}

impl BaseLink for Link {
  #[inline]
  fn new(next_offset: u32, prev_offset: u32) -> Self {
    Self {
      next_offset: AtomicU32::new(next_offset),
      prev_offset: AtomicU32::new(prev_offset),
    }
  }

  #[inline]
  fn store_next_offset(&self, offset: u32, ordering: Ordering) {
    self.next_offset.store(offset, ordering);
  }

  #[inline]
  fn store_prev_offset(&self, offset: u32, ordering: Ordering) {
    self.prev_offset.store(offset, ordering);
  }
}

#[repr(C)]
struct Node<T> {
  // A byte slice is 24 bytes. We are trying to save space here.
  /// Multiple parts of the value are encoded as a single u64 so that it
  /// can be atomically loaded and stored:
  ///   value offset: u32 (bits 0-31)
  ///   value size  : u32 (bits 32-63)
  value: AtomicValuePointer,
  // Immutable. No need to lock to access key.
  key_offset: u32,
  // Immutable. No need to lock to access key.
  key_size_and_height: u32,
  version: u64,
  trailer: PhantomData<T>,
  // ** DO NOT REMOVE BELOW COMMENT**
  // The below field will be attached after the node, have to comment out
  // this field, because each node will not use the full height, the code will
  // not allocate the full size of the tower.
  //
  // Most nodes do not need to use the full height of the tower, since the
  // probability of each successive level decreases exponentially. Because
  // these elements are never accessed, they do not need to be allocated.
  // Therefore, when a node is allocated in the arena, its memory footprint
  // is deliberately truncated to not include unneeded tower elements.
  //
  // All accesses to elements should use CAS operations, with no need to lock.
  // pub(super) tower: [Link; self.opts.max_height],
}

impl<T> core::fmt::Debug for Node<T> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    let (key_size, height) = decode_key_size_and_height(self.key_size_and_height);
    let (value_offset, value_size) = decode_value_pointer(self.value.0.load(Ordering::Relaxed));
    f.debug_struct("Node")
      .field("value_offset", &value_offset)
      .field("value_size", &value_size)
      .field("key_offset", &self.key_offset)
      .field("key_size", &key_size)
      .field("height", &height)
      .finish()
  }
}

impl<T> Node<T> {
  const SIZE: usize = mem::size_of::<Self>();
  const ALIGN: u32 = mem::align_of::<Self>() as u32;

  #[inline]
  fn full(value_offset: u32, max_height: u8) -> Self {
    Self {
      value: AtomicValuePointer::new(value_offset, 0),
      key_offset: 0,
      key_size_and_height: encode_key_size_and_height(0, max_height),
      version: MIN_VERSION,
      trailer: PhantomData,
    }
  }

  #[inline]
  const fn size(max_height: u8) -> usize {
    Self::SIZE + (max_height as usize) * Link::SIZE
  }

  #[inline]
  fn set_version(&mut self, version: Version) {
    self.version = version;
  }

  #[inline]
  fn version(&self) -> Version {
    self.version
  }

  #[inline]
  fn update_value(&self, arena: &Arena, offset: u32, value_size: u32) {
    let (_, old_len) = self.value.swap(offset, value_size);
    if old_len != REMOVE {
      arena.increase_discarded(old_len);
    }
  }

  #[inline]
  fn clear_value(
    &self,
    arena: &Arena,
    success: Ordering,
    failure: Ordering,
  ) -> Result<(), (u32, u32)> {
    self
      .value
      .compare_remove(success, failure)
      .map(|(_, old_len)| {
        if old_len != REMOVE {
          arena.increase_discarded(old_len);
        }
      })
  }
}

impl<T: core::fmt::Debug + Trailer> BaseNode for Node<T> {
  type Link = Link;

  type Trailer = T;

  type ValuePointer = AtomicValuePointer;

  type Pointer = NodePtr<Self::Trailer>;

  fn full(value_offset: u32, max_height: u8) -> Self {
    Self {
      value: AtomicValuePointer::new(value_offset, 0),
      key_offset: 0,
      key_size_and_height: encode_key_size_and_height(0, max_height),
      version: MIN_VERSION,
      trailer: PhantomData,
    }
  }

  #[inline]
  fn value_pointer(&self) -> &Self::ValuePointer {
    &self.value
  }

  #[inline]
  fn set_value_pointer(&mut self, offset: u32, size: u32) {
    self.value = AtomicValuePointer::new(offset, size);
  }

  #[inline]
  fn clear_value<A: BaseAllocator>(
    &self,
    arena: &A,
    success: Ordering,
    failure: Ordering,
  ) -> Result<(), (u32, u32)> {
    self
      .value
      .compare_remove(success, failure)
      .map(|(_, old_len)| {
        if old_len != REMOVE {
          arena.increase_discarded(old_len);
        }
      })
  }

  #[inline]
  fn set_key_size_and_height(&mut self, key_size_and_height: u32) {
    self.key_size_and_height = key_size_and_height;
  }

  #[inline]
  fn set_key_offset(&mut self, key_offset: u32) {
    self.key_offset = key_offset;
  }

  #[inline]
  fn version(&self) -> Version {
    self.version
  }

  #[inline]
  fn set_version(&mut self, version: Version) {
    self.version = version;
  }

  #[inline]
  fn key_size_and_height(&self) -> u32 {
    self.key_size_and_height
  }

  #[inline]
  fn key_offset(&self) -> u32 {
    self.key_offset
  }
}

impl<'a> BaseBytesRefMut for BytesRefMut<'a> {
  fn offset(&self) -> u32 {
    BytesRefMut::offset(self) as u32
  }

  fn capacity(&self) -> u32 {
    BytesRefMut::capacity(self) as u32
  }

  fn memory_offset(&self) -> usize {
    BytesRefMut::memory_offset(self)
  }

  fn memory_capacity(&self) -> usize {
    BytesRefMut::memory_capacity(self)
  }

  fn detach(&mut self) {
    BytesRefMut::detach(self)
  }

  fn as_mut_ptr(&self) -> *mut u8 {
    BytesRefMut::as_mut_ptr(self)
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn flush(&self) -> std::io::Result<()> {
    BytesRefMut::flush(self)
  }
}

impl<'a, T> BaseRefMut<T> for RefMut<'a, T> {
  #[inline]
  fn offset(&self) -> u32 {
    RefMut::offset(self) as u32
  }

  #[inline]
  fn memory_offset(&self) -> usize {
    RefMut::memory_offset(self)
  }

  #[inline]
  fn memory_capacity(&self) -> usize {
    RefMut::memory_capacity(self)
  }

  #[inline]
  unsafe fn detach(&mut self) {
    unsafe { RefMut::detach(self) }
  }

  #[inline]
  unsafe fn write(&mut self, value: T) {
    RefMut::write(self, value)
  }

  #[inline]
  fn as_mut_ptr(&mut self) -> NonNull<T> {
    RefMut::as_mut_ptr(self)
  }
}

///. j
#[derive(Debug)]
pub struct Allocator<N> {
  arena: Arena,
  max_key_size: u32,
  max_value_size: u32,
  max_height: u32,
  _m: PhantomData<N>,
}

impl<N> Allocator<N> {
  #[inline]
  fn refs(&self) -> usize {
    self.arena.refs()
  }
}

impl<N> Clone for Allocator<N> {
  fn clone(&self) -> Self {
    Self {
      arena: self.arena.clone(),
      max_key_size: self.max_key_size,
      max_value_size: self.max_value_size,
      max_height: self.max_height,
      _m: PhantomData,
    }
  }
}

impl<N: BaseNode> BaseAllocator for Allocator<N> {
  type BytesRefMut<'a> = BytesRefMut<'a> where Self: 'a;

  type RefMut<'a, T> = RefMut<'a, T>
  where
    Self: 'a;

  type Header = Meta;

  type Node = N;

  type Trailer = <N as BaseNode>::Trailer;

  fn new(arena_opts: ArenaOptions, opts: Options) -> Self {
    Self {
      arena: Arena::new(arena_opts),
      max_key_size: opts.max_key_size().into(),
      max_value_size: opts.max_value_size(),
      max_height: opts.max_height().into(),
      _m: PhantomData,
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn map_anon(
    arena_opts: rarena_allocator::ArenaOptions,
    mmap_options: MmapOptions,
    opts: Options,
  ) -> std::io::Result<Self> {
    Arena::map_anon(arena_opts, mmap_options).map(|arena| Self {
      arena,
      max_key_size: opts.max_key_size().into(),
      max_value_size: opts.max_value_size(),
      max_height: opts.max_height().into(),
      _m: PhantomData,
    })
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn map_mut<P: AsRef<std::path::Path>>(
    path: P,
    arena_opts: rarena_allocator::ArenaOptions,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    opts: Options,
  ) -> std::io::Result<Self> {
    Arena::map_mut(path, arena_opts, open_options, mmap_options).map(|arena| Self {
      arena,
      max_key_size: opts.max_key_size().into(),
      max_value_size: opts.max_value_size(),
      max_height: opts.max_height().into(),
      _m: PhantomData,
    })
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn map<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    opts: Options,
    magic_version: u16,
  ) -> std::io::Result<Self> {
    Arena::map(path, open_options, mmap_options, magic_version).map(|arena| Self {
      arena,
      max_key_size: opts.max_key_size().into(),
      max_value_size: opts.max_value_size(),
      max_height: opts.max_height().into(),
      _m: PhantomData,
    })
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn map_mut_with_path_builder<PB, E>(
    path_builder: PB,
    arena_opts: rarena_allocator::ArenaOptions,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    opts: Options,
  ) -> Result<Self, Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    Arena::map_mut_with_path_builder(path_builder, arena_opts, open_options, mmap_options).map(
      |arena| Self {
        arena,
        max_key_size: opts.max_key_size().into(),
        max_value_size: opts.max_value_size(),
        max_height: opts.max_height().into(),
        _m: PhantomData,
      },
    )
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn map_with_path_builder<PB, E>(
    path_builder: PB,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    opts: Options,
    magic_version: u16,
  ) -> Result<Self, Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    Arena::map_with_path_builder(path_builder, open_options, mmap_options, magic_version).map(
      |arena| Self {
        arena,
        max_key_size: opts.max_key_size().into(),
        max_value_size: opts.max_value_size(),
        max_height: opts.max_height().into(),
        _m: PhantomData,
      },
    )
  }

  /// Flushes the memory-mapped file to disk.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn flush(&self) -> std::io::Result<()> {
    self.arena.flush()
  }

  /// Flushes the memory-mapped file to disk asynchronously.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn flush_async(&self) -> std::io::Result<()> {
    self.arena.flush_async()
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(windows)))]
  unsafe fn mlock(&self, offset: usize, len: usize) -> std::io::Result<()> {
    self.arena.mlock(offset, len)
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(windows)))]
  unsafe fn munlock(&self, offset: usize, size: usize) -> std::io::Result<()> {
    self.arena.munlock(offset, size)
  }

  #[inline]
  unsafe fn rewind(&self, pos: ArenaPosition) {
    self.arena.rewind(pos)
  }

  fn magic_version(&self) -> u16 {
    self.arena.magic_version()
  }

  fn remaining(&self) -> usize {
    self.arena.remaining()
  }

  fn discarded(&self) -> u32 {
    self.arena.discarded()
  }

  fn allocated(&self) -> u32 {
    self.arena.allocated() as u32
  }

  fn capacity(&self) -> usize {
    self.arena.capacity()
  }

  fn data_offset(&self) -> usize {
    self.arena.data_offset()
  }

  fn read_only(&self) -> bool {
    self.arena.read_only()
  }

  unsafe fn offset(&self, ptr: *const u8) -> usize {
    self.arena.offset(ptr)
  }

  fn align_offset<T>(offset: u32) -> u32 {
    Arena::align_offset::<T>(offset)
  }

  fn alloc_aligned_bytes<T>(
    &self,
    size: u32,
  ) -> Result<Self::BytesRefMut<'_>, rarena_allocator::Error> {
    self.arena.alloc_aligned_bytes::<T>(size)
  }

  fn alloc_bytes(&self, size: u32) -> Result<Self::BytesRefMut<'_>, rarena_allocator::Error> {
    self.arena.alloc_bytes(size)
  }

  unsafe fn alloc<T>(&self) -> Result<Self::RefMut<'_, T>, rarena_allocator::Error> {
    self.arena.alloc::<T>()
  }

  unsafe fn get_aligned_pointer<T>(&self, offset: usize) -> *const T {
    self.arena.get_aligned_pointer(offset)
  }

  unsafe fn get_pointer(&self, offset: usize) -> *const u8 {
    self.arena.get_pointer(offset)
  }

  unsafe fn get_pointer_mut(&self, offset: usize) -> *mut u8 {
    self.arena.get_pointer_mut(offset)
  }

  unsafe fn get_bytes(&self, offset: usize, size: usize) -> &[u8] {
    self.arena.get_bytes(offset, size)
  }

  unsafe fn get_bytes_mut(&self, offset: usize, size: usize) -> &mut [u8] {
    self.arena.get_bytes_mut(offset, size)
  }

  unsafe fn dealloc(&self, offset: u32, size: u32) -> bool {
    self.arena.dealloc(offset, size)
  }

  fn increase_discarded(&self, offset: u32) {
    self.arena.increase_discarded(offset)
  }

  fn refs(&self) -> usize {
    self.arena.refs()
  }

  unsafe fn clear(&self) -> Result<(), ArenaError> {
    self.arena.clear()
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn is_on_disk_and_mmap(&self) -> bool {
    self.arena.is_on_disk_and_mmap()
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn is_ondisk(&self) -> bool {
    self.arena.is_on_disk()
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn is_mmap(&self) -> bool {
    self.arena.is_mmap()
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn flush_range(&self, offset: usize, size: usize) -> std::io::Result<()> {
    self.arena.flush_range(offset, size)
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn page_size(&self) -> usize {
    self.arena.page_size()
  }

  fn max_key_size(&self) -> u32 {
    self.max_key_size
  }

  fn max_value_size(&self) -> u32 {
    self.max_value_size
  }

  fn max_height(&self) -> u32 {
    self.max_height
  }
}
