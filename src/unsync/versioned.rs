use super::*;

#[cfg(any(all(test, not(miri)), all_tests, test_unsync_versioned,))]
mod tests {
  use super::*;

  __container_tests!("unsync_versioned_map": SkipMap);

  __versioned_map_tests!("unsync_versioned_map": SkipMap<Ascend>);
}

type Allocator = GenericAllocator<VersionedMeta, VersionedNode, Arena>;
type SkipList<C> = base::SkipList<Allocator, C>;

node_pointer!(VersionedNode);

/// A node that supports version.
#[repr(C)]
pub struct VersionedNode {
  // A byte slice is 24 bytes. We are trying to save space here.
  /// Multiple parts of the value are encoded as a single u64 so that it
  /// can be atomically loaded and stored:
  ///   value offset: u32 (bits 0-31)
  ///   value size  : u32 (bits 32-63)
  value: UnsyncValuePointer,
  // Immutable. No need to lock to access key.
  key_offset: u32,
  // Immutable. No need to lock to access key.
  key_size_and_height: u32,
  version: u64,
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

impl core::fmt::Debug for VersionedNode {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    let (key_size, height) = decode_key_size_and_height(self.key_size_and_height);
    let (value_offset, value_size) = self.value.load();
    f.debug_struct("Node")
      .field("value_offset", &value_offset)
      .field("value_size", &value_size)
      .field("key_offset", &self.key_offset)
      .field("key_size", &key_size)
      .field("height", &height)
      .finish()
  }
}

impl WithVersion for VersionedNode {}

impl Node for VersionedNode {
  type Link = Link;

  type Trailer = ();

  type ValuePointer = UnsyncValuePointer;

  type Pointer = NodePointer;

  fn full(value_offset: u32, max_height: u8) -> Self {
    Self {
      value: UnsyncValuePointer::new(value_offset, 0),
      key_offset: 0,
      key_size_and_height: encode_key_size_and_height(0, max_height),
      version: MIN_VERSION,
    }
  }

  #[inline]
  fn value_pointer(&self) -> &Self::ValuePointer {
    &self.value
  }

  #[inline]
  fn set_value_pointer(&mut self, offset: u32, size: u32) {
    self.value = UnsyncValuePointer::new(offset, size);
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

/// A fast, ARENA based `SkipMap` that supports multiple versions, forward and backward iteration.
///
/// If you want to use in concurrent environment, you can use [`sync::versioned::SkipMap`].
#[repr(transparent)]
pub struct SkipMap<C = Ascend>(SkipList<C>);

impl<C: Clone> Clone for SkipMap<C> {
  #[inline]
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<C> From<SkipList<C>> for SkipMap<C> {
  #[inline]
  fn from(list: SkipList<C>) -> Self {
    Self(list)
  }
}

impl<C> crate::traits::List for SkipMap<C> {
  type Allocator = Allocator;
  type Comparator = C;

  #[inline]
  fn as_ref(&self) -> &SkipList<Self::Comparator> {
    &self.0
  }

  #[inline]
  fn as_mut(&mut self) -> &mut SkipList<Self::Comparator> {
    &mut self.0
  }
}
