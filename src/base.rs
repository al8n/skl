use core::{
  cmp,
  convert::Infallible,
  marker::PhantomData,
  mem,
  ops::{Bound, RangeBounds},
  ptr::{self, NonNull},
};

use std::boxed::Box;

use crate::{Key, Trailer, VacantBuffer};

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
use error::{bad_magic_version, bad_version, invalid_data};
use options::CompressionPolicy;

use super::{sync::*, Arena, Ascend, Comparator, *};

mod api;
pub use api::*;

use either::Either;

mod error;
pub use error::Error;
mod entry;
pub use entry::*;
mod iterator;
pub use iterator::*;

use rarena_allocator::{BytesRefMut, Error as ArenaError};

#[cfg(test)]
mod tests;

const CURRENT_VERSION: u16 = 0;

/// The tombstone value size, if a node's value size is equal to this value, then it is a tombstone.
const REMOVE: u32 = u32::MAX;

type UpdateOk<'a, 'b, T> = Either<
  Option<VersionedEntryRef<'a, T>>,
  Result<VersionedEntryRef<'a, T>, VersionedEntryRef<'a, T>>,
>;

#[derive(Debug)]
#[repr(C)]
struct Meta {
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

impl Meta {
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
  const fn magic_version(&self) -> u16 {
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
    let version = version.into();
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
    let version = version.into();
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

impl<T> NodePtr<T> {
  const NULL: Self = Self {
    ptr: ptr::null_mut(),
    offset: 0,
  };

  #[inline]
  const fn new(ptr: *mut u8, offset: u32) -> Self {
    Self {
      ptr: ptr.cast(),
      offset,
    }
  }

  #[inline]
  const fn is_null(&self) -> bool {
    self.offset == 0
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

  #[inline]
  unsafe fn tower(&self, arena: &Arena, idx: usize) -> &Link {
    let tower_ptr_offset = self.offset as usize + Node::<T>::SIZE + idx * Link::SIZE;
    let tower_ptr = arena.get_pointer(tower_ptr_offset);
    &*tower_ptr.cast()
  }

  #[inline]
  unsafe fn write_tower(&self, arena: &Arena, idx: usize, prev_offset: u32, next_offset: u32) {
    let tower_ptr_offset = self.offset as usize + Node::<T>::SIZE + idx * Link::SIZE;
    let tower_ptr: *mut Link = arena.get_pointer_mut(tower_ptr_offset).cast();
    *tower_ptr = Link::new(next_offset, prev_offset);
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
  unsafe fn next_offset(&self, arena: &Arena, idx: usize) -> u32 {
    self.tower(arena, idx).next_offset.load(Ordering::Acquire)
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
  unsafe fn prev_offset(&self, arena: &Arena, idx: usize) -> u32 {
    self.tower(arena, idx).prev_offset.load(Ordering::Acquire)
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
  unsafe fn cas_prev_offset(
    &self,
    arena: &Arena,
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
  unsafe fn cas_next_offset(
    &self,
    arena: &Arena,
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
}

#[derive(Debug)]
#[repr(C)]
struct Link {
  next_offset: AtomicU32,
  prev_offset: AtomicU32,
}

impl Link {
  const SIZE: usize = mem::size_of::<Self>();

  #[inline]
  fn new(next_offset: u32, prev_offset: u32) -> Self {
    Self {
      next_offset: AtomicU32::new(next_offset),
      prev_offset: AtomicU32::new(prev_offset),
    }
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
enum NodeState {
  Initialized = 0,
  Committed = 1,
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
  // The state of the node, 0 means initialized but not committed, 1 means committed.
  state: AtomicU8,
  // `u56` (7 bytes) for storing version (MVCC purpose)
  version1: u8,
  version2: u8,
  version3: u8,
  version4: u8,
  version5: u8,
  version6: u8,
  version7: u8,
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
    let [version1, version2, version3, version4, version5, version6, version7] =
      MIN_VERSION.to_le_bytes();
    Self {
      value: AtomicValuePointer::new(value_offset, 0),
      key_offset: 0,
      key_size_and_height: encode_key_size_and_height(0, max_height),
      state: AtomicU8::new(NodeState::Committed as u8),
      version1,
      version2,
      version3,
      version4,
      version5,
      version6,
      version7,
      trailer: PhantomData,
    }
  }

  #[inline]
  const fn size(max_height: u8) -> usize {
    Self::SIZE + (max_height as usize) * Link::SIZE
  }

  #[inline]
  fn is_committed(&self) -> bool {
    self.state.load(Ordering::Acquire) == NodeState::Committed as u8
  }

  #[inline]
  fn init_state(&mut self, ondisk_mmap: bool) {
    if ondisk_mmap {
      self.state = AtomicU8::new(NodeState::Initialized as u8);
    } else {
      self.state = AtomicU8::new(NodeState::Committed as u8);
    }
  }

  #[inline]
  unsafe fn commit(&self, offset: u32, arena: &Arena) -> std::io::Result<()> {
    let h = self.height() as usize;
    let node_size = mem::size_of::<Self>();
    let full_node_size = node_size + h * Link::SIZE;
    self
      .state
      .store(NodeState::Committed as u8, Ordering::Release);
    arena.flush_range(offset as usize, full_node_size)
  }

  #[inline]
  unsafe fn sync(&self, offset: u32, arena: &Arena) -> std::io::Result<()> {
    let h = self.height() as usize;
    let node_size = mem::size_of::<Self>();
    let full_node_size = node_size + h * Link::SIZE;
    arena.flush_range(offset as usize, full_node_size)
  }

  #[inline]
  fn set_version(&mut self, version: Version) {
    let [version1, version2, version3, version4, version5, version6, version7] =
      version.to_le_bytes();
    self.version1 = version1;
    self.version2 = version2;
    self.version3 = version3;
    self.version4 = version4;
    self.version5 = version5;
    self.version6 = version6;
    self.version7 = version7;
  }

  #[inline]
  fn version(&self) -> Version {
    Version::from_le_bytes([
      self.version1,
      self.version2,
      self.version3,
      self.version4,
      self.version5,
      self.version6,
      self.version7,
    ])
  }

  #[inline]
  fn allocate_and_set_value<'a, E>(
    &self,
    arena: &'a Arena,
    trailer: T,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<(), Either<E, Error>> {
    let (value_size, f) = value_builder.into_components();
    let mut bytes = arena
      .alloc_aligned_bytes::<T>(value_size)
      .map_err(|e| Either::Right(e.into()))?;
    let trailer_ptr = bytes.as_mut_ptr().cast::<T>();
    let trailer_offset = bytes.offset();
    let value_offset = trailer_offset + mem::size_of::<T>();

    let mut oval = VacantBuffer::new(value_size as usize, value_offset as u32, unsafe {
      arena.get_bytes_mut(value_offset, value_size as usize)
    });
    f(&mut oval).map_err(Either::Left)?;

    let remaining = oval.remaining();
    let mut discard = 0;
    if remaining != 0
      && unsafe { !arena.dealloc((value_offset + oval.len()) as u32, remaining as u32) }
    {
      discard += remaining;
    }

    bytes.detach();
    unsafe {
      trailer_ptr.write(trailer);
    }

    if discard != 0 {
      arena.increase_discarded(discard as u32);
    }

    let (_, old_len) = self.value.swap(trailer_offset as u32, value_size);
    if old_len != REMOVE {
      arena.increase_discarded(old_len);
    }

    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    {
      if arena.is_on_disk_and_mmap() {
        bytes.flush().map_err(|e| Either::Right(e.into()))?;
      }
    }

    Ok(())
  }

  #[inline]
  fn set_value(&self, arena: &Arena, offset: u32, value_size: u32) {
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

impl<T> Node<T> {
  #[inline]
  const fn key_size(&self) -> u32 {
    decode_key_size_and_height(self.key_size_and_height).0
  }

  #[inline]
  const fn height(&self) -> u8 {
    decode_key_size_and_height(self.key_size_and_height).1
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  const unsafe fn get_key<'a, 'b: 'a>(&'a self, arena: &'b Arena) -> &'b [u8] {
    arena.get_bytes(self.key_offset as usize, self.key_size() as usize)
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[inline]
  unsafe fn get_value<'a, 'b: 'a>(&'a self, arena: &'b Arena) -> Option<&'b [u8]> {
    let (offset, len) = self.value.load(Ordering::Acquire);

    if len == u32::MAX {
      return None;
    }
    let align_offset = Self::align_offset(offset);
    Some(arena.get_bytes(align_offset as usize + mem::size_of::<T>(), len as usize))
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[inline]
  unsafe fn get_value_by_value_offset<'a, 'b: 'a>(
    &'a self,
    arena: &'b Arena,
    offset: u32,
    len: u32,
  ) -> Option<&'b [u8]> {
    if len == u32::MAX {
      return None;
    }

    Some(arena.get_bytes(offset as usize, len as usize))
  }

  #[inline]
  pub(super) fn trailer_offset_and_value_size(&self) -> ValuePartPointer<T> {
    let (offset, len) = self.value.load(Ordering::Acquire);
    let align_offset = Self::align_offset(offset);
    ValuePartPointer::new(align_offset, align_offset + mem::size_of::<T>() as u32, len)
  }

  #[inline]
  const fn align_offset(current_offset: u32) -> u32 {
    let alignment = mem::align_of::<T>() as u32;
    (current_offset + alignment - 1) & !(alignment - 1)
  }
}

impl<T> Node<T> {
  #[inline]
  unsafe fn get_trailer<'a, 'b: 'a>(&'a self, arena: &'b Arena) -> &'b T {
    let (offset, _) = self.value.load(Ordering::Acquire);
    &*arena.get_aligned_pointer(offset as usize)
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[inline]
  unsafe fn get_trailer_by_offset<'a, 'b: 'a>(&'a self, arena: &'b Arena, offset: u32) -> &'b T {
    &*arena.get_aligned_pointer::<T>(offset as usize)
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[inline]
  unsafe fn get_value_and_trailer_with_pointer<'a, 'b: 'a>(
    &'a self,
    arena: &'b Arena,
  ) -> (&'b T, Option<&'b [u8]>, ValuePartPointer<T>) {
    let (offset, len) = self.value.load(Ordering::Acquire);
    let ptr = arena.get_aligned_pointer(offset as usize);

    let align_offset = Arena::align_offset::<T>(offset);
    let trailer = &*ptr;

    if len == u32::MAX {
      return (
        trailer,
        None,
        ValuePartPointer::new(offset, align_offset + mem::size_of::<T>() as u32, len),
      );
    }

    let value_offset = align_offset + mem::size_of::<T>() as u32;
    (
      trailer,
      Some(arena.get_bytes(value_offset as usize, len as usize)),
      ValuePartPointer::new(offset, value_offset as u32, len),
    )
  }
}

/// A node allocated by the [`Arena`], but not be linked to the [`SkipList`].
///
/// It is used to help users implement atomic batch insertion or deletion logic.
///
/// **NOTE:** If this node is not linked to the [`SkipList`] through [`insert_node`](SkipList::insert_node), it is better to deallocate it to let the [`Arena`] reuse the memory.
#[must_use = "UnlinkedNode should be either linked to the SkipList or deallocated."]
pub struct UnlinkedNode<'a, T> {
  arena: &'a Arena,
  ptr: NodePtr<T>,
  deallocator: Deallocator,
  height: u32,
  version: Version,
}

impl<'a, T> core::fmt::Debug for UnlinkedNode<'a, T> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("UnlinkedNode")
      .field("version", &self.version)
      .field("key", &self.key())
      .field("value", &self.value())
      .finish()
  }
}

impl<'a, T> UnlinkedNode<'a, T> {
  #[inline]
  const fn new(
    arena: &'a Arena,
    ptr: NodePtr<T>,
    height: u32,
    version: Version,
    deallocator: Deallocator,
  ) -> Self {
    Self {
      arena,
      ptr,
      deallocator,
      height,
      version,
    }
  }

  /// Deallocates the unlinked node, let the [`Arena`] reuse the memory.
  #[inline]
  pub fn dealloc(self) {
    self.deallocator.dealloc(self.arena)
  }

  /// Returns the height of the node.
  #[inline]
  pub const fn height(&self) -> u32 {
    self.height
  }

  /// Returns the version of the node.
  #[inline]
  pub const fn version(&self) -> Version {
    self.version
  }

  /// Returns the key of the node.
  #[inline]
  pub fn key(&self) -> &[u8] {
    // Safety: the node is allocated by the arena.
    unsafe { self.ptr.as_ref().get_key(self.arena) }
  }

  /// Returns the value of the node.
  #[inline]
  pub fn value(&self) -> Option<&[u8]> {
    // Safety: the node is allocated by the arena.
    unsafe { self.ptr.as_ref().get_value(self.arena) }
  }
}

impl<'a, T: Trailer> UnlinkedNode<'a, T> {
  /// Returns the trailer of the node.
  #[inline]
  pub fn trailer(&self) -> &T {
    // Safety: the node is allocated by the arena.
    unsafe { self.ptr.as_ref().get_trailer(self.arena) }
  }
}

/// A fast, cocnurrent map implementation based on skiplist that supports forward
/// and backward iteration.
#[derive(Debug)]
pub struct SkipList<C = Ascend, T = ()> {
  arena: Arena,
  meta: NonNull<Meta>,
  head: NodePtr<T>,
  tail: NodePtr<T>,
  data_offset: u32,
  on_disk: bool,
  opts: Options,
  /// If set to true by tests, then extra delays are added to make it easier to
  /// detect unusual race conditions.
  #[cfg(all(test, feature = "std"))]
  yield_now: bool,

  cmp: C,
}

// Safety: SkipList is Sync and Send
unsafe impl<T: Send, C: Comparator + Send> Send for SkipList<C, T> {}
unsafe impl<T: Sync, C: Comparator + Sync> Sync for SkipList<C, T> {}

impl<C: Clone, T> Clone for SkipList<C, T> {
  fn clone(&self) -> Self {
    Self {
      arena: self.arena.clone(),
      meta: self.meta,
      on_disk: self.on_disk,
      head: self.head,
      tail: self.tail,
      data_offset: self.data_offset,
      opts: self.opts,
      #[cfg(all(test, feature = "std"))]
      yield_now: self.yield_now,
      cmp: self.cmp.clone(),
    }
  }
}

impl<C, T> Drop for SkipList<C, T> {
  fn drop(&mut self) {
    if self.arena.refs() == 1 {
      if !self.opts.unify() {
        unsafe {
          let _ = Box::from_raw(self.meta.as_ptr());
        }
      }

      #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(windows)))]
      if self.arena.is_mmap() {
        let _ = unsafe { self.arena.munlock(0, self.arena.page_size()) };
      }
    }
  }
}

impl<C, T> SkipList<C, T> {
  fn new_in(arena: Arena, cmp: C, opts: Options) -> Result<Self, Error> {
    let data_offset = Self::check_capacity(&arena, opts.max_height().into())?;
    if arena.read_only() {
      let (meta, head, tail) = Self::get_pointers(&arena);

      return Ok(Self::construct(
        arena,
        meta,
        head,
        tail,
        data_offset,
        opts,
        cmp,
      ));
    }

    let meta = if opts.unify() {
      Self::allocate_meta(&arena, opts.magic_version())?
    } else {
      unsafe {
        NonNull::new_unchecked(Box::into_raw(Box::new(Meta {
          max_version: AtomicU64::new(0),
          min_version: AtomicU64::new(0),
          height: AtomicU8::new(1),
          len: AtomicU32::new(0),
          magic_version: opts.magic_version(),
          reserved_byte: 0,
        })))
      }
    };

    let max_height: u8 = opts.max_height().into();
    let head = Self::allocate_full_node(&arena, max_height)?;
    let tail = Self::allocate_full_node(&arena, max_height)?;

    // Safety:
    // We will always allocate enough space for the head node and the tail node.
    unsafe {
      // Link all head/tail levels together.
      for i in 0..(max_height as usize) {
        let head_link = head.tower(&arena, i);
        let tail_link = tail.tower(&arena, i);
        head_link.next_offset.store(tail.offset, Ordering::Relaxed);
        tail_link.prev_offset.store(head.offset, Ordering::Relaxed);
      }
    }

    Ok(Self::construct(
      arena,
      meta,
      head,
      tail,
      data_offset,
      opts,
      cmp,
    ))
  }

  /// Checks if the arena has enough capacity to store the skiplist,
  /// and returns the data offset.
  #[inline]
  const fn check_capacity(arena: &Arena, max_height: u8) -> Result<u32, Error> {
    let offset = arena.data_offset();

    let alignment = mem::align_of::<Meta>();
    let meta_offset = (offset + alignment - 1) & !(alignment - 1);
    let meta_end = meta_offset + mem::size_of::<Meta>();

    let alignment = mem::align_of::<Node<T>>();
    let head_offset = (meta_end + alignment - 1) & !(alignment - 1);
    let head_end =
      head_offset + mem::size_of::<Node<T>>() + mem::size_of::<Link>() * max_height as usize;

    let trailer_alignment = mem::align_of::<T>();
    let trailer_size = mem::size_of::<T>();
    let trailer_end = if trailer_size != 0 {
      let trailer_offset = (head_end + trailer_alignment - 1) & !(trailer_alignment - 1);
      trailer_offset + trailer_size
    } else {
      head_end
    };

    let tail_offset = (trailer_end + alignment - 1) & !(alignment - 1);
    let tail_end =
      tail_offset + mem::size_of::<Node<T>>() + mem::size_of::<Link>() * max_height as usize;
    let trailer_end = if trailer_size != 0 {
      let trailer_offset = (tail_end + trailer_alignment - 1) & !(trailer_alignment - 1);
      trailer_offset + trailer_size
    } else {
      tail_end
    };
    if trailer_end > arena.capacity() {
      return Err(Error::ArenaTooSmall);
    }

    Ok(trailer_end as u32)
  }

  #[inline]
  fn allocate_pure_node(&self, height: u32) -> Result<BytesRefMut, ArenaError> {
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    {
      let ondisk_mmap = self.arena.is_on_disk_and_mmap();
      if ondisk_mmap {
        self
          .arena
          .alloc_aligned_bytes_within_page::<Node<T>>(height * Link::SIZE as u32)
      } else {
        self
          .arena
          .alloc_aligned_bytes::<Node<T>>(height * Link::SIZE as u32)
      }
    }

    #[cfg(not(all(feature = "memmap", not(target_family = "wasm"))))]
    {
      self
        .arena
        .alloc_aligned_bytes::<Node<T>>(height * Link::SIZE as u32)
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  fn msync_new_entry(
    &self,
    // (offset, size)
    (node_offset, node_size): (u32, u32),
    // (offset, size)
    key: Option<(u32, u32)>,
    // (offset, size)
    value: Option<(u32, u32)>,
  ) -> Result<(), Error> {
    use arrayvec::ArrayVec;

    if self.arena.is_on_disk_and_mmap() {
      fn calculate_page_bounds(offset: u32, size: u32, page_size: u32) -> (u32, u32) {
        let start_page = offset / page_size;
        let end_page = (offset + size).saturating_sub(1) / page_size;
        (start_page, end_page)
      }

      let page_size = self.arena.page_size() as u32;
      let mut ranges = ArrayVec::<(u32, u32), 3>::new_const();
      ranges.push(calculate_page_bounds(node_offset, node_size, page_size));

      if let Some((offset, size)) = key {
        ranges.push(calculate_page_bounds(offset, size, page_size));
      }

      if let Some((offset, size)) = value {
        ranges.push(calculate_page_bounds(offset, size, page_size));
      }

      let len = ranges.len();

      match len {
        1 => {
          return self
            .arena
            .flush_range(node_offset as usize, node_size as usize)
            .map_err(Into::into);
        }
        2..=3 => {
          // Sort ranges by start page
          ranges.sort_by_key(|&(start, _)| start);

          let mut merged_ranges = ArrayVec::<(u32, u32), 3>::new_const();

          for (start, end) in ranges {
            match merged_ranges.last_mut() {
              None => {
                merged_ranges.push((start, end));
              }
              // no overlap
              Some((_, last_end)) if *last_end < start => {
                merged_ranges.push((start, end));
              }
              // overlap
              Some((_, last)) => {
                *last = (*last).max(end);
              }
            }
          }

          for (start, end) in merged_ranges {
            let spo = (start * page_size) as usize;
            let epo = (end * page_size) as usize;
            self.arena.flush_range(spo, (epo - spo).max(1))?;
          }

          return Ok(());
        }
        _ => unreachable!(),
      }
    }

    Ok(())
  }

  /// Allocates a `Node`, key, trailer and value
  fn allocate_entry_node<'a, 'b: 'a, E>(
    &'a self,
    version: Version,
    height: u32,
    trailer: T,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<(NodePtr<T>, Deallocator), Either<E, Error>> {
    let (key_size, kf) = key_builder.into_components();
    let (value_size, vf) = value_builder.into_components();

    self
      .check_node_size(height, key_size.to_u32(), value_size)
      .map_err(Either::Right)?;

    unsafe {
      let mut node = self
        .allocate_pure_node(height)
        .map_err(|e| Either::Right(e.into()))?;
      let node_ptr = node.as_mut_ptr().cast::<Node<T>>();
      let node_offset = node.offset();

      let mut key = self
        .arena
        .alloc_bytes(key_size.to_u32())
        .map_err(|e| Either::Right(e.into()))?;
      let key_offset = key.offset();
      let key_cap = key.capacity();
      let mut trailer_and_value = self
        .arena
        .alloc_aligned_bytes::<T>(value_size)
        .map_err(|e| Either::Right(e.into()))?;
      let trailer_offset = trailer_and_value.offset();
      let trailer_ptr = trailer_and_value.as_mut_ptr().cast::<T>();
      trailer_ptr.write(trailer);

      let value_offset = (trailer_offset + mem::size_of::<T>()) as u32;

      // Safety: the node is well aligned
      let node_ref = &mut *node_ptr;
      node_ref.value = AtomicValuePointer::new(trailer_offset as u32, value_size);
      node_ref.key_offset = key_offset as u32;
      node_ref.key_size_and_height = encode_key_size_and_height(key_cap as u32, height as u8);
      node_ref.set_version(version);

      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      let ondisk_mmap = self.arena.is_on_disk_and_mmap();
      #[cfg(not(all(feature = "memmap", not(target_family = "wasm"))))]
      let ondisk_mmap = false;
      node_ref.init_state(ondisk_mmap);

      key.detach();
      let (_, key_deallocate_info) = self
        .fill_vacant_key(key_cap as u32, key_offset as u32, kf)
        .map_err(Either::Left)?;
      trailer_and_value.detach();
      let (_, value_deallocate_info) = self
        .fill_vacant_value(
          trailer_offset as u32,
          trailer_and_value.capacity() as u32,
          value_size,
          value_offset,
          vf,
        )
        .map_err(Either::Left)?;
      node.detach();

      let deallocator = Deallocator {
        node: Some(Pointer::new(node_offset as u32, node.capacity() as u32)),
        key: Some(key_deallocate_info),
        value: Some(value_deallocate_info),
      };

      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      if let Err(e) = self.msync_new_entry(
        (node_offset as u32, node.capacity() as u32),
        Some((key_offset as u32, key.capacity() as u32)),
        Some((
          trailer_and_value.memory_offset() as u32,
          trailer_and_value.memory_capacity() as u32,
        )),
      ) {
        deallocator.dealloc(&self.arena);

        return Err(Either::Right(e));
      }

      Ok((NodePtr::new(node_ptr as _, node_offset as u32), deallocator))
    }
  }

  /// Allocates a `Node` and trailer
  fn allocate_node_in<'a, 'b: 'a, E>(
    &'a self,
    version: Version,
    height: u32,
    trailer: T,
    key_offset: u32,
    key_size: u32,
    value_size: u32,
  ) -> Result<(NodePtr<T>, Deallocator), Either<E, Error>> {
    self
      .check_node_size(height, key_size, value_size)
      .map_err(Either::Right)?;

    unsafe {
      let mut node = self
        .arena
        .alloc_aligned_bytes::<Node<T>>(height * Link::SIZE as u32)
        .map_err(|e| Either::Right(e.into()))?;
      let node_ptr = node.as_mut_ptr().cast::<Node<T>>();
      let node_offset = node.offset();

      let mut trailer_ref = self
        .arena
        .alloc::<T>()
        .map_err(|e| Either::Right(e.into()))?;
      let trailer_offset = trailer_ref.offset();
      trailer_ref.write(trailer);

      // Safety: the node is well aligned
      let node_ref = &mut *node_ptr;
      node_ref.value = AtomicValuePointer::new(trailer_offset as u32, value_size);
      node_ref.key_offset = key_offset;
      node_ref.key_size_and_height = encode_key_size_and_height(key_size, height as u8);
      node_ref.set_version(version);

      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      let ondisk_mmap = self.arena.is_on_disk_and_mmap();
      #[cfg(not(all(feature = "memmap", not(target_family = "wasm"))))]
      let ondisk_mmap = false;
      node_ref.init_state(ondisk_mmap);

      trailer_ref.detach();
      node.detach();

      let deallocator = Deallocator {
        node: Some(Pointer::new(node_offset as u32, node.capacity() as u32)),
        key: None,
        value: Some(Pointer::new(
          trailer_offset as u32,
          mem::size_of::<T>() as u32,
        )),
      };

      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      if let Err(e) = self.msync_new_entry(
        (node_offset as u32, node.capacity() as u32),
        None,
        Some((
          trailer_ref.memory_offset() as u32,
          trailer_ref.memory_size() as u32,
        )),
      ) {
        deallocator.dealloc(&self.arena);
        return Err(Either::Right(e));
      }

      Ok((NodePtr::new(node_ptr as _, node_offset as u32), deallocator))
    }
  }

  /// Allocates a `Node`, key and trailer
  fn allocate_key_node<'a, 'b: 'a, E>(
    &'a self,
    version: Version,
    height: u32,
    trailer: T,
    key_size: u32,
    kf: impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>,
    value_size: u32,
  ) -> Result<(NodePtr<T>, Deallocator), Either<E, Error>> {
    self
      .check_node_size(height, key_size, value_size)
      .map_err(Either::Right)?;

    unsafe {
      let mut node = self
        .arena
        .alloc_aligned_bytes::<Node<T>>(height * Link::SIZE as u32)
        .map_err(|e| Either::Right(e.into()))?;
      let node_ptr = node.as_mut_ptr().cast::<Node<T>>();
      let node_offset = node.offset();

      let mut key = self
        .arena
        .alloc_bytes(key_size)
        .map_err(|e| Either::Right(e.into()))?;
      let key_offset = key.offset();
      let key_cap = key.capacity();

      let mut trailer_ref = self
        .arena
        .alloc::<T>()
        .map_err(|e| Either::Right(e.into()))?;
      let trailer_offset = trailer_ref.offset();
      trailer_ref.write(trailer);

      // Safety: the node is well aligned
      let node_ref = &mut *node_ptr;
      node_ref.value = AtomicValuePointer::new(trailer_offset as u32, value_size);
      node_ref.key_offset = key_offset as u32;
      node_ref.key_size_and_height = encode_key_size_and_height(key_cap as u32, height as u8);
      node_ref.set_version(version);

      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      let ondisk_mmap = self.arena.is_on_disk_and_mmap();
      #[cfg(not(all(feature = "memmap", not(target_family = "wasm"))))]
      let ondisk_mmap = false;
      node_ref.init_state(ondisk_mmap);

      key.detach();
      let (_, key_deallocate_info) = self
        .fill_vacant_key(key_cap as u32, key_offset as u32, kf)
        .map_err(Either::Left)?;

      trailer_ref.detach();
      node.detach();

      let deallocator = Deallocator {
        node: Some(Pointer::new(node_offset as u32, node.capacity() as u32)),
        key: Some(key_deallocate_info),
        value: Some(Pointer::new(
          trailer_offset as u32,
          mem::size_of::<T>() as u32,
        )),
      };

      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      if let Err(e) = self.msync_new_entry(
        (node_offset as u32, node.capacity() as u32),
        Some((key_offset as u32, key.capacity() as u32)),
        Some((
          trailer_ref.memory_offset() as u32,
          trailer_ref.memory_size() as u32,
        )),
      ) {
        deallocator.dealloc(&self.arena);
        return Err(Either::Right(e));
      }

      Ok((NodePtr::new(node_ptr as _, node_offset as u32), deallocator))
    }
  }

  /// Allocates a `Node`, trailer and value
  fn allocate_value_node<'a, 'b: 'a, E>(
    &'a self,
    version: Version,
    height: u32,
    trailer: T,
    key_size: u32,
    key_offset: u32,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>,
  ) -> Result<(NodePtr<T>, Deallocator), Either<E, Error>> {
    let (value_size, vf) = value_builder.into_components();
    self
      .check_node_size(height, key_size, value_size)
      .map_err(Either::Right)?;

    unsafe {
      let mut node = self
        .arena
        .alloc_aligned_bytes::<Node<T>>(height * Link::SIZE as u32)
        .map_err(|e| Either::Right(e.into()))?;
      let node_ptr = node.as_mut_ptr().cast::<Node<T>>();
      let node_offset = node.offset();

      let mut trailer_and_value = self
        .arena
        .alloc_aligned_bytes::<T>(value_size)
        .map_err(|e| Either::Right(e.into()))?;
      let trailer_offset = trailer_and_value.offset();
      let trailer_ptr = trailer_and_value.as_mut_ptr().cast::<T>();
      trailer_ptr.write(trailer);
      let value_offset = (trailer_offset + mem::size_of::<T>()) as u32;

      // Safety: the node is well aligned
      let node_ref = &mut *node_ptr;
      node_ref.value = AtomicValuePointer::new(trailer_offset as u32, value_size);
      node_ref.key_offset = key_offset;
      node_ref.key_size_and_height = encode_key_size_and_height(key_size, height as u8);
      node_ref.set_version(version);
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      let ondisk_mmap = self.arena.is_on_disk_and_mmap();
      #[cfg(not(all(feature = "memmap", not(target_family = "wasm"))))]
      let ondisk_mmap = false;
      node_ref.init_state(ondisk_mmap);

      trailer_and_value.detach();
      let (_, value_deallocate_info) = self
        .fill_vacant_value(
          trailer_offset as u32,
          trailer_and_value.capacity() as u32,
          value_size,
          value_offset,
          vf,
        )
        .map_err(Either::Left)?;

      node.detach();

      let deallocator = Deallocator {
        node: Some(Pointer::new(node_offset as u32, node.capacity() as u32)),
        key: None,
        value: Some(value_deallocate_info),
      };

      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      if let Err(e) = self.msync_new_entry(
        (node_offset as u32, node.capacity() as u32),
        None,
        Some((
          trailer_and_value.memory_offset() as u32,
          trailer_and_value.memory_capacity() as u32,
        )),
      ) {
        deallocator.dealloc(&self.arena);
        return Err(Either::Right(e));
      }

      Ok((NodePtr::new(node_ptr as _, node_offset as u32), deallocator))
    }
  }

  fn allocate_full_node(arena: &Arena, max_height: u8) -> Result<NodePtr<T>, ArenaError> {
    // Safety: node, links and trailer do not need to be dropped, and they are recoverable.
    unsafe {
      let mut node =
        arena.alloc_aligned_bytes::<Node<T>>(((max_height as usize) * Link::SIZE) as u32)?;

      // Safety: node and trailer do not need to be dropped.
      node.detach();

      let node_ptr = node.as_mut_ptr().cast::<Node<T>>();
      let node_offset = node.offset();

      let trailer_offset = if mem::size_of::<T>() != 0 {
        let mut trailer = arena.alloc::<T>()?;
        trailer.detach();
        trailer.offset()
      } else {
        arena.allocated()
      };

      let node = &mut *node_ptr;
      *node = Node::<T>::full(trailer_offset as u32, max_height);

      Ok(NodePtr::new(node_ptr as _, node_offset as u32))
    }
  }

  #[inline]
  fn allocate_meta(arena: &Arena, magic_version: u16) -> Result<NonNull<Meta>, ArenaError> {
    // Safety: meta does not need to be dropped, and it is recoverable.
    unsafe {
      let mut meta = arena.alloc::<Meta>()?;
      meta.detach();

      meta.write(Meta {
        max_version: AtomicU64::new(0),
        min_version: AtomicU64::new(0),
        height: AtomicU8::new(1),
        len: AtomicU32::new(0),
        magic_version,
        reserved_byte: 0,
      });
      Ok(meta.as_mut_ptr())
    }
  }

  #[inline]
  unsafe fn fill_vacant_key<'a, E>(
    &'a self,
    size: u32,
    offset: u32,
    f: impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>,
  ) -> Result<(u32, Pointer), E> {
    let buf = self.arena.get_bytes_mut(offset as usize, size as usize);
    let mut oval = VacantBuffer::new(size as usize, offset, buf);
    if let Err(e) = f(&mut oval) {
      self.arena.dealloc(offset, size);
      return Err(e);
    }

    let len = oval.len();
    let remaining = oval.remaining();
    if remaining != 0 {
      #[cfg(feature = "tracing")]
      tracing::warn!("vacant value is not fully filled, remaining {remaining} bytes");
      let deallocated = self.arena.dealloc(offset + len as u32, remaining as u32);
      if deallocated {
        return Ok((
          oval.len() as u32,
          Pointer::new(offset, size - remaining as u32),
        ));
      }
    }
    Ok((oval.len() as u32, Pointer::new(offset, size)))
  }

  #[inline]
  unsafe fn fill_vacant_value<'a, E>(
    &'a self,
    offset: u32,
    size: u32,
    value_size: u32,
    value_offset: u32,
    f: impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>,
  ) -> Result<(u32, Pointer), E> {
    let buf = self
      .arena
      .get_bytes_mut(value_offset as usize, value_size as usize);
    let mut oval = VacantBuffer::new(value_size as usize, value_offset, buf);
    if let Err(e) = f(&mut oval) {
      self.arena.dealloc(offset, size);
      return Err(e);
    }

    let len = oval.len();
    let remaining = oval.remaining();
    if remaining != 0 {
      #[cfg(feature = "tracing")]
      tracing::warn!("vacant value is not fully filled, remaining {remaining} bytes");
      let deallocated = self
        .arena
        .dealloc(value_offset + len as u32, remaining as u32);

      if deallocated {
        return Ok((
          oval.len() as u32,
          Pointer::new(offset, size - remaining as u32),
        ));
      }
    }

    Ok((oval.len() as u32, Pointer::new(offset, size)))
  }

  #[inline]
  fn get_pointers(arena: &Arena) -> (NonNull<Meta>, NodePtr<T>, NodePtr<T>) {
    unsafe {
      let offset = arena.data_offset();
      let meta = arena.get_aligned_pointer::<Meta>(offset);

      let offset = arena.offset(meta as _) + mem::size_of::<Meta>();
      let head_ptr = arena.get_aligned_pointer::<Node<T>>(offset);
      let head_offset = arena.offset(head_ptr as _);
      let head = NodePtr::new(head_ptr as _, head_offset as u32);

      let (trailer_offset, _) = head.as_ref().value.load(Ordering::Relaxed);
      let offset = trailer_offset as usize + mem::size_of::<T>();
      let tail_ptr = arena.get_aligned_pointer::<Node<T>>(offset);
      let tail_offset = arena.offset(tail_ptr as _);
      let tail = NodePtr::new(tail_ptr as _, tail_offset as u32);
      (NonNull::new_unchecked(meta as _), head, tail)
    }
  }

  #[inline]
  fn check_node_size(&self, height: u32, key_size: u32, mut value_size: u32) -> Result<(), Error> {
    let max_height: u32 = self.opts.max_height().into();
    if height < 1 || height > max_height {
      panic!("height cannot be less than one or greater than the max height");
    }

    let max_key_size: u32 = self.opts.max_key_size().into();
    if key_size > max_key_size {
      return Err(Error::KeyTooLarge(key_size as u64));
    }

    // if value_size is u32::MAX, it means that the value is removed.
    value_size = if value_size == u32::MAX {
      0
    } else {
      value_size
    };

    if value_size > self.opts.max_value_size() {
      return Err(Error::ValueTooLarge(value_size as u64));
    }

    let entry_size = (value_size as u64 + key_size as u64) + Node::<T>::size(height as u8) as u64;
    if entry_size > u32::MAX as u64 {
      return Err(Error::EntryTooLarge(entry_size));
    }

    Ok(())
  }

  #[inline]
  fn construct(
    arena: Arena,
    meta: NonNull<Meta>,
    head: NodePtr<T>,
    tail: NodePtr<T>,
    data_offset: u32,
    opts: Options,
    cmp: C,
  ) -> Self {
    Self {
      on_disk: arena.is_on_disk(),
      arena,
      meta,
      head,
      tail,
      data_offset,
      opts,
      #[cfg(all(test, feature = "std"))]
      yield_now: false,
      cmp,
    }
  }

  #[inline]
  const fn meta(&self) -> &Meta {
    // Safety: the pointer is well aligned and initialized.
    unsafe { self.meta.as_ref() }
  }
}

impl<C, T: Trailer> SkipList<C, T> {
  fn new_node<'a, 'b: 'a, E>(
    &'a self,
    version: Version,
    height: u32,
    key: &Key<'a, 'b>,
    value_builder: Option<ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>>,
    trailer: T,
  ) -> Result<(NodePtr<T>, Deallocator), Either<E, Error>> {
    let (nd, deallocator) = match key {
      Key::Occupied(key) => {
        let kb = KeyBuilder::new(KeySize::from_u32_unchecked(key.len() as u32), |buf| {
          buf.write(key).expect("buffer must be large enough for key");
          Ok(())
        });
        let vb = value_builder.unwrap();
        self.allocate_entry_node(version, height, trailer, kb, vb)?
      }
      Key::Vacant(key) => self.allocate_value_node(
        version,
        height,
        trailer,
        key.len() as u32,
        key.offset,
        value_builder.unwrap(),
      )?,
      Key::Pointer { offset, len, .. } => self.allocate_value_node(
        version,
        height,
        trailer,
        *len,
        *offset,
        value_builder.unwrap(),
      )?,
      Key::Remove(key) => self.allocate_key_node(
        version,
        height,
        trailer,
        key.len() as u32,
        |buf| {
          buf.write(key).expect("buffer must be large enough for key");
          Ok(())
        },
        REMOVE,
      )?,
      Key::RemoveVacant(key) => self.allocate_node_in(
        version,
        height,
        trailer,
        key.offset,
        key.len() as u32,
        REMOVE,
      )?,
      Key::RemovePointer { offset, len, .. } => {
        self.allocate_node_in(version, height, trailer, *offset, *len, REMOVE)?
      }
    };

    // Try to increase self.height via CAS.
    let mut list_height = self.height();
    while height as u8 > list_height {
      match self.meta().height.compare_exchange_weak(
        list_height,
        height as u8,
        Ordering::SeqCst,
        Ordering::Acquire,
      ) {
        // Successfully increased skiplist.height.
        Ok(_) => break,
        Err(h) => list_height = h,
      }
    }
    Ok((nd, deallocator))
  }
}

impl<C: Comparator, T: Trailer> SkipList<C, T> {
  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[inline]
  unsafe fn get_prev(&self, mut nd: NodePtr<T>, height: usize, ignore_invalid_trailer: bool) -> NodePtr<T> {
    loop {
      if nd.is_null() {
        return NodePtr::NULL;
      }

      if nd.ptr == self.head.ptr {
        return self.head;
      }

      let offset = nd.prev_offset(&self.arena, height);
      let ptr = self.arena.get_pointer(offset as usize);
      let prev = NodePtr::new(ptr as _, offset);
      let prev_node = prev.as_ref();
      // the prev node is not committed, skip it for now.
      if !prev_node.is_committed() {
        nd = prev;
        continue;
      }

      if ignore_invalid_trailer && !prev_node.get_trailer(&self.arena).is_valid() {
        nd = prev;
        continue;
      }

      return prev;
    }
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[inline]
  unsafe fn get_next(&self, mut nptr: NodePtr<T>, height: usize, ignore_invalid_trailer: bool) -> NodePtr<T> {
    loop {
      if nptr.is_null() {
        return NodePtr::NULL;
      }

      if nptr.ptr == self.tail.ptr {
        return self.tail;
      }

      let offset = nptr.next_offset(&self.arena, height);
      let ptr = self.arena.get_pointer(offset as usize);

      let next = NodePtr::new(ptr as _, offset);
      let next_node = next.as_ref();
      // the next node is not committed, skip it for now.
      if !next_node.is_committed() {
        nptr = next;
        continue;
      }

      if ignore_invalid_trailer && !next_node.get_trailer(&self.arena).is_valid() {
        nptr = next;
        continue;
      }

      return next;
    }
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[inline]
  unsafe fn get_next_allow_uncommitted(&self, nptr: NodePtr<T>, height: usize) -> NodePtr<T> {
    if nptr.is_null() {
      return NodePtr::NULL;
    }

    let offset = nptr.next_offset(&self.arena, height);
    let ptr = self.arena.get_pointer(offset as usize);

    NodePtr::new(ptr as _, offset)
  }

  /// Returns the first entry in the map.
  fn first_in(&self, version: Version, ignore_invalid_trailer: bool) -> Option<NodePtr<T>> {
    // Safety: head node was definitely allocated by self.arena
    let nd = unsafe { self.get_next(self.head, 0, ignore_invalid_trailer) };

    if nd.is_null() || nd.ptr == self.tail.ptr {
      return None;
    }

    unsafe {
      let node = nd.as_ref();
      let curr_key = node.get_key(&self.arena);
      self.ge(version, curr_key, ignore_invalid_trailer)
    }
  }

  /// Returns the last entry in the map.
  fn last_in(&self, version: Version, ignore_invalid_trailer: bool) -> Option<NodePtr<T>> {
    // Safety: tail node was definitely allocated by self.arena
    let nd = unsafe { self.get_prev(self.tail, 0, ignore_invalid_trailer) };

    if nd.is_null() || nd.ptr == self.head.ptr {
      return None;
    }

    unsafe {
      let node = nd.as_ref();
      let curr_key = node.get_key(&self.arena);
      self.le(version, curr_key, ignore_invalid_trailer)
    }
  }

  /// Returns the entry greater or equal to the given key, if it exists.
  ///
  /// e.g.
  ///
  /// - If k1 < k2 < k3, key is equal to k1, then the entry contains k2 will be returned.
  /// - If k1 < k2 < k3, and k1 < key < k2, then the entry contains k2 will be returned.
  fn gt<'a, 'b: 'a>(&'a self, version: Version, key: &'b [u8], ignore_invalid_trailer: bool) -> Option<NodePtr<T>> {
    unsafe {
      let (n, _) = self.find_near(Version::MIN, key, false, false, ignore_invalid_trailer); // find the key with the max version.

      let n = n?;

      if n.is_null() || n.ptr == self.tail.ptr {
        return None;
      }

      self.find_next_max_version(n, version, ignore_invalid_trailer)
    }
  }

  /// Returns the entry less than the given key, if it exists.
  ///
  /// e.g.
  ///
  /// - If k1 < k2 < k3, and key is equal to k3, then the entry contains k2 will be returned.
  /// - If k1 < k2 < k3, and k2 < key < k3, then the entry contains k2 will be returned.
  fn lt<'a, 'b: 'a>(&'a self, version: Version, key: &'b [u8], ignore_invalid_trailer: bool) -> Option<NodePtr<T>> {
    unsafe {
      let (n, _) = self.find_near(Version::MAX, key, true, false, ignore_invalid_trailer); // find less or equal.

      let n = n?;
      if n.is_null() || n.ptr == self.head.ptr {
        return None;
      }

      self.find_prev_max_version(n, version, ignore_invalid_trailer)
    }
  }

  /// Returns the entry greater than or equal to the given key, if it exists.
  ///
  /// e.g.
  ///
  /// - If k1 < k2 < k3, key is equal to k1, then the entry contains k1 will be returned.
  /// - If k1 < k2 < k3, and k1 < key < k2, then the entry contains k2 will be returned.
  fn ge<'a, 'b: 'a>(&'a self, version: Version, key: &'b [u8], ignore_invalid_trailer: bool) -> Option<NodePtr<T>> {
    unsafe {
      let (n, _) = self.find_near(Version::MAX, key, false, true, ignore_invalid_trailer); // find the key with the max version.

      let n = n?;

      if n.is_null() || n.ptr == self.tail.ptr {
        return None;
      }

      self.find_next_max_version(n, version, ignore_invalid_trailer)
    }
  }

  /// Returns the entry less than or equal to the given key, if it exists.
  ///
  /// e.g.
  ///
  /// - If k1 < k2 < k3, and key is equal to k3, then the entry contains k3 will be returned.
  /// - If k1 < k2 < k3, and k2 < key < k3, then the entry contains k2 will be returned.
  fn le<'a, 'b: 'a>(&'a self, version: Version, key: &'b [u8], ignore_invalid_trailer: bool) -> Option<NodePtr<T>> {
    unsafe {
      let (n, _) = self.find_near(Version::MIN, key, true, true, ignore_invalid_trailer); // find less or equal.

      let n = n?;
      if n.is_null() || n.ptr == self.head.ptr {
        return None;
      }

      self.find_prev_max_version(n, version, ignore_invalid_trailer)
    }
  }

  unsafe fn find_prev_max_version(
    &self,
    mut curr: NodePtr<T>,
    version: Version,
    ignore_invalid_trailer: bool
  ) -> Option<NodePtr<T>> {
    let mut prev = self.get_prev(curr, 0, ignore_invalid_trailer);

    loop {
      let curr_node = curr.as_ref();
      let curr_key = curr_node.get_key(&self.arena);
      // if the current version is greater than the given version, we should return.
      let version_cmp = curr_node.version().cmp(&version);
      if version_cmp == cmp::Ordering::Greater {
        return None;
      }

      if prev.is_null() || prev.ptr == self.head.ptr {
        if let cmp::Ordering::Less | cmp::Ordering::Equal = version_cmp {
          return Some(curr);
        }

        return None;
      }

      let prev_node = prev.as_ref();
      let prev_key = prev_node.get_key(&self.arena);
      if self.cmp.compare(prev_key, curr_key) == cmp::Ordering::Less {
        return Some(curr);
      }

      let version_cmp = prev_node.version().cmp(&version);

      if version_cmp == cmp::Ordering::Equal {
        return Some(prev);
      }

      if version_cmp == cmp::Ordering::Greater {
        return Some(curr);
      }

      curr = prev;
      prev = self.get_prev(curr, 0, ignore_invalid_trailer);
    }
  }

  unsafe fn find_next_max_version(
    &self,
    mut curr: NodePtr<T>,
    version: Version,
    ignore_invalid_trailer: bool
  ) -> Option<NodePtr<T>> {
    let mut next = self.get_next(curr, 0, ignore_invalid_trailer);

    loop {
      let curr_node = curr.as_ref();
      let curr_key = curr_node.get_key(&self.arena);
      // if the current version is less or equal to the given version, we should return.
      let version_cmp = curr_node.version().cmp(&version);
      if let cmp::Ordering::Less | cmp::Ordering::Equal = version_cmp {
        return Some(curr);
      }

      if next.is_null() || next.ptr == self.head.ptr {
        if let cmp::Ordering::Less | cmp::Ordering::Equal = version_cmp {
          return Some(curr);
        }

        return None;
      }

      let next_node = next.as_ref();
      let next_key = next_node.get_key(&self.arena);
      let version_cmp = next_node.version().cmp(&version);
      if self.cmp.compare(next_key, curr_key) == cmp::Ordering::Greater {
        if let cmp::Ordering::Less | cmp::Ordering::Equal = version_cmp {
          return Some(curr);
        }

        return None;
      }

      if let cmp::Ordering::Less | cmp::Ordering::Equal = version_cmp {
        if next.ptr == self.tail.ptr {
          return None;
        }

        return Some(next);
      }

      curr = next;
      next = self.get_next(curr, 0, ignore_invalid_trailer);
    }
  }

  /// finds the node near to key.
  /// If less=true, it finds rightmost node such that node.key < key (if allow_equal=false) or
  /// node.key <= key (if allow_equal=true).
  /// If less=false, it finds leftmost node such that node.key > key (if allow_equal=false) or
  /// node.key >= key (if allow_equal=true).
  /// Returns the node found. The bool returned is true if the node has key equal to given key.
  unsafe fn find_near(
    &self,
    version: Version,
    key: &[u8],
    less: bool,
    allow_equal: bool,
    ignore_invalid_trailer: bool,
  ) -> (Option<NodePtr<T>>, bool) {
    let mut x = self.head;
    let mut level = self.height() as usize - 1;

    loop {
      // Assume x.key < key.
      let next = self.get_next(x, level, ignore_invalid_trailer);
      let is_next_null = next.is_null();

      // if next is not committed, we should continue to find.
      if !is_next_null && !next.as_ref().is_committed() {
        x = next;
        continue;
      }

      if is_next_null || next.ptr == self.tail.ptr {
        // x.key < key < END OF LIST
        if level > 0 {
          // Can descend further to iterate closer to the end.
          level -= 1;
          continue;
        }

        // level == 0. Can't descend further. Let's return something that makes sense.
        if !less {
          return (None, false);
        }

        // Try to return x. Make sure it is not a head node.
        if x.ptr == self.head.ptr {
          return (None, false);
        }

        return (Some(x), false);
      }

      let next_node = next.as_ref();
      let next_key = next_node.get_key(&self.arena);
      let cmp = self
        .cmp
        .compare(key, next_key)
        .then_with(|| next_node.version().cmp(&version));

      match cmp {
        cmp::Ordering::Greater => {
          // x.key < next.key < key. We can continue to move right.
          x = next;
          continue;
        }
        cmp::Ordering::Equal => {
          // x.key < key == next.key.
          if allow_equal {
            return (Some(next), true);
          }

          if !less {
            // We want >, so go to base level to grab the next bigger node.
            return (Some(self.get_next(next, 0, ignore_invalid_trailer)), false);
          }

          // We want <. If not base level, we should go closer in the next level.
          if level > 0 {
            level -= 1;
            continue;
          }

          // On base level, Return x.
          return (Some(x), false);
        }
        // In other words, x.key < key < next.
        cmp::Ordering::Less => {
          if level > 0 {
            level -= 1;
            continue;
          }

          // On base level. Need to return something.
          if !less {
            return (Some(next), false);
          }

          // Try to return x. Make sure it is not a head node.
          if x.ptr == self.head.ptr {
            return (None, false);
          }

          return (Some(x), false);
        }
      }
    }
  }

  /// Find the place to insert the key.
  ///
  /// ## Safety:
  /// - All of splices in the inserter must be contains node ptrs are allocated by the current skip map.
  unsafe fn find_splice<'a, 'b: 'a>(
    &'a self,
    version: Version,
    key: &'b [u8],
    ins: &mut Inserter<T>,
    returned_when_found: bool,
  ) -> (bool, Option<Pointer>, Option<NodePtr<T>>) {
    let list_height = self.height() as u32;
    let mut level = 0;

    let mut prev = self.head;
    if ins.height < list_height {
      // Our cached height is less than the list height, which means there were
      // inserts that increased the height of the list. Recompute the splice from
      // scratch.
      ins.height = list_height;
      level = ins.height as usize;
    } else {
      // Our cached height is equal to the list height.
      while level < list_height as usize {
        let spl = &ins.spl[level];
        if self.get_next_allow_uncommitted(spl.prev, level).ptr != spl.next.ptr {
          level += 1;
          // One or more nodes have been inserted between the splice at this
          // level.
          continue;
        }

        if spl.prev.ptr != self.head.ptr && !self.key_is_after_node(spl.prev, version, key) {
          // Key lies before splice.
          level = list_height as usize;
          break;
        }

        if spl.next.ptr != self.tail.ptr && !self.key_is_after_node(spl.next, version, key) {
          // Key lies after splice.
          level = list_height as usize;
          break;
        }

        // The splice brackets the key!
        prev = spl.prev;
        break;
      }
    }

    let mut found = false;
    let mut found_key = None;
    for lvl in (0..level).rev() {
      let mut fr = self.find_splice_for_level(version, key, lvl, prev);
      if fr.splice.next.is_null() {
        fr.splice.next = self.tail;
      }

      found = fr.found;
      if let Some(key) = fr.found_key {
        found_key.get_or_insert(key);
      }
      if found && returned_when_found {
        return (found, found_key, fr.curr);
      }
      ins.spl[lvl] = fr.splice;
    }

    (found, found_key, None)
  }

  /// Find the splice for the given level.
  ///
  /// # Safety
  /// - `level` is less than `MAX_HEIGHT`.
  /// - `start` must be allocated by self's arena.
  unsafe fn find_splice_for_level(
    &self,
    version: Version,
    key: &[u8],
    level: usize,
    start: NodePtr<T>,
  ) -> FindResult<T> {
    let mut prev = start;

    loop {
      // Assume prev.key < key.
      let next = self.get_next_allow_uncommitted(prev, level);
      if next.ptr == self.tail.ptr {
        // Tail node, so done.
        return FindResult {
          splice: Splice { prev, next },
          found: false,
          found_key: None,
          curr: None,
        };
      }

      // offset is not zero, so we can safely dereference the next node ptr.
      let next_node = next.as_ref();
      let next_key = next_node.get_key(&self.arena);

      let cmp = self.cmp.compare(key, next_key);

      let mut found_key = None;

      match cmp {
        cmp::Ordering::Equal => {
          found_key = Some(Pointer {
            offset: next_node.key_offset,
            size: next_node.key_size(),
            height: Some(next_node.height()),
          });
        }
        cmp::Ordering::Greater | cmp::Ordering::Less if found_key.is_none() => {
          found_key = self.try_get_pointer(next_node, next_key, key);
        }
        _ => {}
      }

      match cmp.then_with(|| next_node.version().cmp(&version)) {
        // We are done for this level, since prev.key < key < next.key.
        cmp::Ordering::Less => {
          return FindResult {
            splice: Splice { prev, next },
            found: false,
            found_key,
            curr: None,
          };
        }
        // Keep moving right on this level.
        cmp::Ordering::Greater => prev = next,
        cmp::Ordering::Equal => {
          return FindResult {
            splice: Splice { prev, next },
            found: next_node.is_committed(),
            found_key,
            curr: Some(next),
          };
        }
      }
    }
  }

  fn try_get_pointer(&self, next_node: &Node<T>, next_key: &[u8], key: &[u8]) -> Option<Pointer> {
    match self.opts.compression_policy() {
      CompressionPolicy::Fast => {
        if next_key.starts_with(key) {
          return Some(Pointer {
            offset: next_node.key_offset,
            size: key.len() as u32,
            height: Some(next_node.height()),
          });
        }
      }
      CompressionPolicy::High => {
        if let Some(idx) = memchr::memmem::find(next_key, key) {
          return Some(Pointer {
            offset: next_node.key_offset + idx as u32,
            size: key.len() as u32,
            height: Some(next_node.height()),
          });
        }
      }
    }
    None
  }

  /// ## Safety
  /// - The caller must ensure that the node is allocated by the arena.
  /// - The caller must ensure that the node is not null.
  unsafe fn key_is_after_node(&self, nd: NodePtr<T>, version: Version, key: &[u8]) -> bool {
    let nd = &*nd.ptr;
    let nd_key = self
      .arena
      .get_bytes(nd.key_offset as usize, nd.key_size() as usize);

    match self.cmp.compare(nd_key, key) {
      cmp::Ordering::Less => true,
      cmp::Ordering::Greater => false,
      cmp::Ordering::Equal => {
        matches!(version.cmp(&nd.version()), cmp::Ordering::Less)
      }
    }
  }

  fn fetch_vacant_key<'a, 'b: 'a, E>(
    &'a self,
    key_size: u32,
    key: impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>,
  ) -> Result<VacantBuffer<'a>, Either<E, Error>> {
    let (key_offset, key_size) = self
      .arena
      .alloc_bytes(key_size)
      .map(|mut b| {
        b.detach();
        (b.offset(), b.capacity())
      })
      .map_err(|e| Either::Right(e.into()))?;

    let mut vk = unsafe {
      VacantBuffer::new(
        key_size,
        key_offset as u32,
        self.arena.get_bytes_mut(key_offset, key_size),
      )
    };
    key(&mut vk)
      .map_err(|e| {
        unsafe {
          self.arena.dealloc(key_offset as u32, key_size as u32);
        }
        Either::Left(e)
      })
      .and_then(|_| {
        #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
        {
          let ondisk_mmap = self.arena.is_on_disk_and_mmap();
          if ondisk_mmap {
            self.arena.flush_range(key_offset, key_size).map_err(|e| Either::Right(e.into()))?;
          }
        }
        Ok(vk)
      })
  }

  #[inline]
  fn check_height_and_ro(&self, height: Height) -> Result<(), Error> {
    if self.arena.read_only() {
      return Err(Error::read_only());
    }

    let max_height = self.opts.max_height();

    if height > max_height {
      return Err(Error::invalid_height(height, max_height));
    }
    Ok(())
  }

  fn get_or_allocate_unlinked_node_in<'a, 'b: 'a, E>(
    &'a self,
    version: impl Into<Version>,
    trailer: T,
    height: u32,
    key: Key<'a, 'b>,
    value_builder: Option<ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>>,
    mut ins: Inserter<'a, T>,
  ) -> Result<Either<UnlinkedNode<'a, T>, VersionedEntryRef<'a, T>>, Either<E, Error>> {
    let version = version.into();
    let is_remove = key.is_remove();

    // Safety: a fresh new Inserter, so safe here
    let (found, found_key, ptr) =
      unsafe { self.find_splice(version, key.as_ref(), &mut ins, true) };

    if found {
      let node_ptr = ptr.expect("the NodePtr cannot be `None` when we found");
      let old = VersionedEntryRef::from_node(node_ptr, &self.arena);
      let is_old_removed = old.is_removed();

      if !is_old_removed {
        key.on_fail(&self.arena);
        return Ok(Either::Right(old));
      }

      if is_old_removed && is_remove {
        key.on_fail(&self.arena);
        return Ok(Either::Right(old));
      }
    }

    let k = match found_key {
      None => key,
      Some(k) => {
        key.on_fail(&self.arena);

        if is_remove {
          Key::remove_pointer(&self.arena, k)
        } else {
          Key::pointer(&self.arena, k)
        }
      }
    };

    let (nd, deallocator) = self
      .new_node(version, height, &k, value_builder, trailer)
      .inspect_err(|_| {
        k.on_fail(&self.arena);
      })?;

    Ok(Either::Left(UnlinkedNode::new(
      &self.arena,
      nd,
      height,
      version,
      deallocator,
    )))
  }

  fn allocate_unlinked_node_in<'a, 'b: 'a, E>(
    &'a self,
    version: impl Into<Version>,
    trailer: T,
    height: u32,
    key: Key<'a, 'b>,
    value_builder: Option<ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>>,
    mut ins: Inserter<'a, T>,
  ) -> Result<UnlinkedNode<T>, Either<E, Error>> {
    let version = version.into();
    // Safety: a fresh new Inserter, so safe here
    let (_, found_key, _) = unsafe { self.find_splice(version, key.as_ref(), &mut ins, true) };

    let k = match found_key {
      None => key,
      Some(k) => {
        let is_remove = key.is_remove();
        key.on_fail(&self.arena);

        if is_remove {
          Key::remove_pointer(&self.arena, k)
        } else {
          Key::pointer(&self.arena, k)
        }
      }
    };

    let (nd, deallocator) = self
      .new_node(version, height, &k, value_builder, trailer)
      .inspect_err(|_| {
        k.on_fail(&self.arena);
      })?;

    Ok(UnlinkedNode::new(
      &self.arena,
      nd,
      height,
      version,
      deallocator,
    ))
  }

  fn link_node_in<'a, 'b: 'a>(
    &'a self,
    node: UnlinkedNode<'a, T>,
    success: Ordering,
    failure: Ordering,
    upsert: bool,
  ) -> Result<UpdateOk<'a, 'b, T>, Error> {
    assert!(
      ptr::addr_eq(&self.arena, node.arena),
      "unlinked node is not from the same arena as the skipmap"
    );
    let version = node.version();

    // SAFETY: node is allocated by the arena, so safe here
    let unlinked = unsafe { node.ptr.as_ref() };
    let value = unsafe { unlinked.get_value(&self.arena) };
    let mut ins = Inserter::default();

    // Safety: a fresh new Inserter, so safe here
    unsafe {
      let (found, found_key, ptr) =
        self.find_splice(version, unlinked.get_key(&self.arena), &mut ins, true);

      if found {
        let node_ptr = ptr.expect("the NodePtr cannot be `None` when we found");
        let k = found_key.expect("the key cannot be `None` when we found");
        let old = VersionedEntryRef::from_node(node_ptr, &self.arena);

        if upsert {
          let (value_offset, value_size) = unlinked.value.load(Ordering::Acquire);
          match value {
            Some(_) => {
              return self.upsert_value(
                old,
                node_ptr,
                &Key::pointer(&self.arena, k),
                value_offset,
                value_size,
                success,
                failure,
              );
            }
            None => {
              return self.upsert_value(
                old,
                node_ptr,
                &Key::remove_pointer(&self.arena, k),
                value_offset,
                value_size,
                success,
                failure,
              );
            }
          }
        }

        return Ok(Either::Left(if old.is_removed() {
          None
        } else {
          Some(old)
        }));
      }
    }

    self.link_in(node, success, failure, upsert, ins)
  }

  #[allow(clippy::too_many_arguments)]
  fn update<'a, 'b: 'a, E>(
    &'a self,
    version: impl Into<Version>,
    trailer: T,
    height: u32,
    key: Key<'a, 'b>,
    value_builder: Option<ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>>,
    success: Ordering,
    failure: Ordering,
    mut ins: Inserter<'a, T>,
    upsert: bool,
  ) -> Result<UpdateOk<'a, 'b, T>, Either<E, Error>> {
    let version = version.into();
    let is_remove = key.is_remove();

    // Safety: a fresh new Inserter, so safe here
    let found_key = unsafe {
      let (found, found_key, ptr) = self.find_splice(version, key.as_ref(), &mut ins, true);
      if found_key.is_some() {
        key.on_fail(&self.arena);
      }

      if found {
        let node_ptr = ptr.expect("the NodePtr cannot be `None` when we found");
        let k = found_key.expect("the key cannot be `None` when we found");
        let old = VersionedEntryRef::from_node(node_ptr, &self.arena);

        if upsert {
          return self.upsert(
            old,
            node_ptr,
            &if is_remove {
              Key::remove_pointer(&self.arena, k)
            } else {
              Key::pointer(&self.arena, k)
            },
            trailer,
            value_builder,
            success,
            failure,
          );
        }

        return Ok(Either::Left(if old.is_removed() {
          None
        } else {
          Some(old)
        }));
      }

      found_key
    };

    #[cfg(all(test, feature = "std"))]
    if self.yield_now {
      // Add delay to make it easier to test race between this thread
      // and another thread that sees the intermediate state between
      // finding the splice and using it.
      std::thread::yield_now();
    }

    let k = match found_key {
      None => key,
      Some(k) => {
        if is_remove {
          Key::remove_pointer(&self.arena, k)
        } else {
          Key::pointer(&self.arena, k)
        }
      }
    };

    let (nd, deallocator) = self
      .new_node(version, height, &k, value_builder, trailer)
      .inspect_err(|_| {
        k.on_fail(&self.arena);
      })?;

    self
      .link_in(
        UnlinkedNode::new(&self.arena, nd, height, version, deallocator),
        success,
        failure,
        upsert,
        ins,
      )
      .map_err(Either::Right)
  }

  fn link_in<'a, 'b: 'a>(
    &'a self,
    node: UnlinkedNode<'a, T>,
    success: Ordering,
    failure: Ordering,
    upsert: bool,
    mut ins: Inserter<'a, T>,
  ) -> Result<UpdateOk<'a, 'b, T>, Error> {
    let is_removed = node.value().is_none();
    let UnlinkedNode {
      arena,
      ptr: nd,
      mut deallocator,
      height,
      version,
    } = node;

    // We always insert from the base level and up. After you add a node in base
    // level, we cannot create a node in the level above because it would have
    // discovered the node in the base level.
    let mut invalid_data_splice = false;

    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    let ondisk_mmap = self.arena.is_on_disk_and_mmap();

    for i in 0..(height as usize) {
      let mut prev = ins.spl[i].prev;
      let mut next = ins.spl[i].next;

      if prev.is_null() {
        // New node increased the height of the skiplist, so assume that the
        // new level has not yet been populated.
        if !next.is_null() {
          panic!("next is expected to be nil, since prev is nil");
        }

        prev = self.head;
        next = self.tail;
      }

      // +----------------+     +------------+     +----------------+
      // |      prev      |     |     nd     |     |      next      |
      // | prevNextOffset |---->|            |     |                |
      // |                |<----| prevOffset |     |                |
      // |                |     | nextOffset |---->|                |
      // |                |     |            |<----| nextPrevOffset |
      // +----------------+     +------------+     +----------------+
      //
      // 1. Initialize prevOffset and nextOffset to point to prev and next.
      // 2. CAS prevNextOffset to repoint from next to nd.
      // 3. CAS nextPrevOffset to repoint from prev to nd.
      unsafe {
        loop {
          let prev_offset = prev.offset;
          let next_offset = next.offset;
          nd.write_tower(&self.arena, i, prev_offset, next_offset);

          #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
          if ondisk_mmap {
            nd.as_ref().sync(nd.offset, &self.arena)?;
          }

          // Check whether next has an updated link to prev. If it does not,
          // that can mean one of two things:
          //   1. The thread that added the next node hasn't yet had a chance
          //      to add the prev link (but will shortly).
          //   2. Another thread has added a new node between prev and next.
          //
          // Safety: we already check next is not null
          let next_prev_offset = next.prev_offset(&self.arena, i);
          if next_prev_offset != prev_offset {
            // Determine whether #1 or #2 is true by checking whether prev
            // is still pointing to next. As long as the atomic operations
            // have at least acquire/release semantics (no need for
            // sequential consistency), this works, as it is equivalent to
            // the "publication safety" pattern.
            let prev_next_offset = prev.next_offset(&self.arena, i);
            if prev_next_offset == next_offset {
              // Ok, case #1 is true, so help the other thread along by
              // updating the next node's prev link.
              let _ = next.cas_prev_offset(
                &self.arena,
                i,
                next_prev_offset,
                prev_offset,
                Ordering::SeqCst,
                Ordering::Acquire,
              );
            }
          }

          match prev.cas_next_offset(
            &self.arena,
            i,
            next.offset,
            nd.offset,
            Ordering::SeqCst,
            Ordering::Acquire,
          ) {
            Ok(_) => {
              // Managed to insert nd between prev and next, so update the next
              // node's prev link and go to the next level.
              #[cfg(all(test, feature = "std"))]
              if self.yield_now {
                // Add delay to make it easier to test race between this thread
                // and another thread that sees the intermediate state between
                // setting next and setting prev.
                std::thread::yield_now();
              }

              #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
              if ondisk_mmap {
                prev.as_ref().sync(prev.offset, &self.arena)?;
              }

              #[cfg(not(all(feature = "memmap", not(target_family = "wasm"))))]
              let _ = next.cas_prev_offset(
                &self.arena,
                i,
                prev_offset,
                nd.offset,
                Ordering::SeqCst,
                Ordering::Acquire,
              );

              #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
              if next
                .cas_prev_offset(
                  &self.arena,
                  i,
                  prev_offset,
                  nd.offset,
                  Ordering::SeqCst,
                  Ordering::Acquire,
                )
                .is_ok()
                && ondisk_mmap
              {
                next.as_ref().sync(next.offset, &self.arena)?;
              }

              break;
            }
            Err(_) => {
              let unlinked_node = nd.as_ref();

              // CAS failed. We need to recompute prev and next. It is unlikely to
              // be helpful to try to use a different level as we redo the search,
              // because it is unlikely that lots of nodes are inserted between prev
              // and next.
              let fr = self.find_splice_for_level(version, unlinked_node.get_key(arena), i, prev);
              if fr.found {
                if i != 0 {
                  panic!("how can another thread have inserted a node at a non-base level?");
                }

                let node_ptr = fr
                  .curr
                  .expect("the current should not be `None` when we found");
                let old = VersionedEntryRef::from_node(node_ptr, &self.arena);

                if upsert {
                  let curr = nd.as_ref();
                  let (new_value_offset, new_value_size) = curr.value.load(Ordering::Acquire);
                  deallocator.dealloc_node_and_key(&self.arena);

                  return self.upsert_value(
                    old,
                    node_ptr,
                    &if is_removed {
                      Key::remove_pointer(&self.arena, fr.found_key.unwrap())
                    } else {
                      Key::pointer(&self.arena, fr.found_key.unwrap())
                    },
                    new_value_offset,
                    new_value_size,
                    success,
                    failure,
                  );
                }

                deallocator.dealloc(&self.arena);
                return Ok(Either::Left(if old.is_removed() {
                  None
                } else {
                  Some(old)
                }));
              }

              if let Some(p) = fr.found_key {
                // if key is already in the underlying allocator, we should deallocate the key
                // in deallocator, and let the underlying allocator reclaim it, so that we do not store the same key twice.
                if deallocator.key.is_some() {
                  let node = nd.as_mut();
                  node.key_offset = p.offset;
                  node.key_size_and_height = encode_key_size_and_height(p.size, p.height.unwrap());
                  deallocator.dealloc_key_by_ref(arena)
                }
              }

              invalid_data_splice = true;
              prev = fr.splice.prev;
              next = fr.splice.next;
            }
          }
        }
      }
    }

    // If we had to recompute the splice for a level, invalidate the entire
    // cached splice.
    if invalid_data_splice {
      ins.height = 0;
    } else {
      // The splice was valid. We inserted a node between spl[i].prev and
      // spl[i].next. Optimistically update spl[i].prev for use in a subsequent
      // call to add.
      for i in 0..(height as usize) {
        ins.spl[i].prev = nd;
      }
    }
    self.meta().increase_len();
    self.meta().update_max_version(version);
    self.meta().update_min_version(version);

    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    if ondisk_mmap {
      unsafe {
        nd.as_mut().commit(nd.offset, &self.arena)?;
      }
    }

    Ok(Either::Left(None))
  }

  #[allow(clippy::too_many_arguments)]
  unsafe fn upsert_value<'a, 'b: 'a>(
    &'a self,
    old: VersionedEntryRef<'a, T>,
    old_node_ptr: NodePtr<T>,
    key: &Key<'a, 'b>,
    value_offset: u32,
    value_size: u32,
    success: Ordering,
    failure: Ordering,
  ) -> Result<UpdateOk<'a, 'b, T>, Error> {
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    let ondisk_mmap = self.arena.is_on_disk_and_mmap();
    match key {
      Key::Occupied(_) | Key::Vacant(_) | Key::Pointer { .. } => {
        let old_node = old_node_ptr.as_ref();
        old_node.set_value(&self.arena, value_offset, value_size);

        #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
        {
          if ondisk_mmap {
            old_node.sync(old_node_ptr.offset, &self.arena)?;
          }
        }

        Ok(Either::Left(if old.is_removed() {
          None
        } else {
          Some(old)
        }))
      }
      Key::Remove(_) | Key::RemoveVacant(_) | Key::RemovePointer { .. } => {
        let node = old_node_ptr.as_ref();
        match node.clear_value(&self.arena, success, failure) {
          Ok(_) => {
            #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
            {
              if ondisk_mmap {
                node.sync(old_node_ptr.offset, &self.arena)?;
              }
            }

            Ok(Either::Left(None))
          }
          Err((offset, len)) => Ok(Either::Right(Err(
            VersionedEntryRef::from_node_with_pointer(
              old_node_ptr,
              &self.arena,
              ValuePartPointer::new(
                offset,
                Arena::align_offset::<T>(offset) + mem::size_of::<T>() as u32,
                len,
              ),
            ),
          ))),
        }
      }
    }
  }

  #[allow(clippy::too_many_arguments)]
  unsafe fn upsert<'a, 'b: 'a, E>(
    &'a self,
    old: VersionedEntryRef<'a, T>,
    old_node_ptr: NodePtr<T>,
    key: &Key<'a, 'b>,
    trailer: T,
    value_builder: Option<ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>>>,
    success: Ordering,
    failure: Ordering,
  ) -> Result<UpdateOk<'a, 'b, T>, Either<E, Error>> {
    match key {
      Key::Occupied(_) | Key::Vacant(_) | Key::Pointer { .. } => old_node_ptr
        .as_ref()
        .allocate_and_set_value(&self.arena, trailer, value_builder.unwrap())
        .map(|_| Either::Left(if old.is_removed() { None } else { Some(old) })),
      Key::Remove(_) | Key::RemoveVacant(_) | Key::RemovePointer { .. } => {
        let node = old_node_ptr.as_ref();
        match node.clear_value(&self.arena, success, failure) {
          Ok(_) => Ok(Either::Left(None)),
          Err((offset, len)) => Ok(Either::Right(Err(
            VersionedEntryRef::from_node_with_pointer(
              old_node_ptr,
              &self.arena,
              ValuePartPointer::new(
                offset,
                Arena::align_offset::<T>(offset) + mem::size_of::<T>() as u32,
                len,
              ),
            ),
          ))),
        }
      }
    }
  }
}

/// A helper struct for caching splice information
pub struct Inserter<'a, T> {
  spl: [Splice<T>; super::MAX_HEIGHT],
  height: u32,
  _m: core::marker::PhantomData<&'a ()>,
}

impl<'a, T> Default for Inserter<'a, T> {
  #[inline]
  fn default() -> Self {
    Self {
      spl: [
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
      ],
      height: 0,
      _m: core::marker::PhantomData,
    }
  }
}

#[derive(Debug, Clone, Copy)]
struct Splice<T> {
  prev: NodePtr<T>,
  next: NodePtr<T>,
}

impl<T> Default for Splice<T> {
  #[inline]
  fn default() -> Self {
    Self {
      prev: NodePtr::NULL,
      next: NodePtr::NULL,
    }
  }
}

struct Deallocator {
  node: Option<Pointer>,
  key: Option<Pointer>,
  value: Option<Pointer>,
}

impl Deallocator {
  #[inline]
  fn dealloc(self, arena: &Arena) {
    unsafe {
      if let Some(ptr) = self.node {
        arena.dealloc(ptr.offset, ptr.size);
      }

      if let Some(ptr) = self.key {
        arena.dealloc(ptr.offset, ptr.size);
      }

      if let Some(ptr) = self.value {
        arena.dealloc(ptr.offset, ptr.size);
      }
    }
  }

  #[inline]
  fn dealloc_node_and_key(self, arena: &Arena) {
    unsafe {
      if let Some(ptr) = self.node {
        arena.dealloc(ptr.offset, ptr.size);
      }

      if let Some(ptr) = self.key {
        arena.dealloc(ptr.offset, ptr.size);
      }
    }
  }

  #[inline]
  fn dealloc_key_by_ref(&mut self, arena: &Arena) {
    if let Some(ptr) = self.key.take() {
      unsafe {
        arena.dealloc(ptr.offset, ptr.size);
      }
    }
  }
}

struct Pointer {
  offset: u32,
  size: u32,
  height: Option<u8>,
}

impl Pointer {
  #[inline]
  const fn new(offset: u32, size: u32) -> Self {
    Self {
      offset,
      size,
      height: None,
    }
  }
}

impl<'a, 'b: 'a> Key<'a, 'b> {
  #[inline]
  const fn pointer(arena: &'a super::Arena, pointer: Pointer) -> Self {
    Self::Pointer {
      arena,
      offset: pointer.offset,
      len: pointer.size,
    }
  }

  #[inline]
  const fn remove_pointer(arena: &'a super::Arena, pointer: Pointer) -> Self {
    Self::RemovePointer {
      arena,
      offset: pointer.offset,
      len: pointer.size,
    }
  }
}

struct FindResult<T> {
  // both key and version are equal.
  found: bool,
  // only key is equal.
  found_key: Option<Pointer>,
  splice: Splice<T>,
  curr: Option<NodePtr<T>>,
}

#[inline]
const fn encode_value_pointer(offset: u32, val_size: u32) -> u64 {
  (val_size as u64) << 32 | offset as u64
}

#[inline]
const fn decode_value_pointer(value: u64) -> (u32, u32) {
  let offset = value as u32;
  let val_size = (value >> 32) as u32;
  (offset, val_size)
}

#[inline]
const fn encode_key_size_and_height(key_size: u32, height: u8) -> u32 {
  // first 27 bits for key_size, last 5 bits for height.
  key_size << 5 | height as u32
}

#[inline]
const fn decode_key_size_and_height(size: u32) -> (u32, u8) {
  let key_size = size >> 5;
  let height = (size & 0b11111) as u8;
  (key_size, height)
}
