use core::marker::PhantomData;

use super::*;

type Allocator<T> = GenericAllocator<Meta, TrailedNode<T>, Arena>;
type SkipList<T, C> = base::SkipList<Allocator<T>, C>;

node_pointer!(TrailedNode<T>);

/// A node that supports trailer.
#[repr(C)]
pub struct TrailedNode<T> {
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

impl<T> core::fmt::Debug for TrailedNode<T> {
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

impl<T: Trailer> WithTrailer for TrailedNode<T> {}

impl<T: Trailer> Node for TrailedNode<T> {
  type Link = Link;

  type Trailer = T;

  type ValuePointer = AtomicValuePointer;

  type Pointer = NodePointer<Self::Trailer>;

  fn full(value_offset: u32, max_height: u8) -> Self {
    Self {
      value: AtomicValuePointer::new(value_offset, 0),
      key_offset: 0,
      key_size_and_height: encode_key_size_and_height(0, max_height),
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
  fn clear_value<A: super::Allocator>(
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
    0
  }

  #[inline]
  fn set_version(&mut self, _: Version) {}

  #[inline]
  fn key_size_and_height(&self) -> u32 {
    self.key_size_and_height
  }

  #[inline]
  fn key_offset(&self) -> u32 {
    self.key_offset
  }
}

/// A fast, lock-free, thread-safe ARENA based `SkipMap` that supports trailed structure, forward and backward iteration.
///
/// If you want to use in non-concurrent environment, you can use [`unsync::trailed::SkipMap`].
#[repr(transparent)]
pub struct SkipMap<T: Trailer = (), C = Ascend>(SkipList<T, C>);

impl<T: Trailer, C: Clone> Clone for SkipMap<T, C> {
  #[inline]
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<T: Trailer, C> From<SkipList<T, C>> for SkipMap<T, C> {
  #[inline]
  fn from(list: SkipList<T, C>) -> Self {
    Self(list)
  }
}

impl<T: Trailer, C> crate::traits::List for SkipMap<T, C> {
  type Allocator = Allocator<T>;

  type Comparator = C;

  #[inline]
  fn as_ref(&self) -> &SkipList<T, Self::Comparator> {
    &self.0
  }

  #[inline]
  fn as_mut(&mut self) -> &mut SkipList<T, Self::Comparator> {
    &mut self.0
  }
}

impl<T: Trailer> SkipMap<T> {
  #[cfg(all(test, feature = "std"))]
  #[inline]
  pub(crate) fn with_yield_now(self) -> Self {
    Self(self.0.with_yield_now())
  }
}
