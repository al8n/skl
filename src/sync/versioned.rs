use super::*;

#[cfg(any(all(test, not(miri)), all_tests, test_sync_versioned,))]
mod tests {
  use super::*;

  __container_tests!("sync_versioned_map": SkipMap);

  __versioned_map_tests!("sync_versioned_map": SkipMap<Ascend>);
}

#[cfg(any(all(test, not(miri)), all_tests, test_sync_versioned_concurrent,))]
mod concurrent_tests {
  use super::*;

  __versioned_map_tests!(go "sync_versioned_map": SkipMap<Ascend>);
}

type Allocator = GenericAllocator<VersionedMeta, VersionedNode, Arena>;
type SkipList<C> = base::SkipList<Allocator, C>;

node!(
  /// A node that supports version.
  struct VersionedNode {
    version: u64 = MIN_VERSION;

    {
      type Link = Link;
      type Trailer = ();
      type ValuePointer = AtomicValuePointer;
      type Pointer = NodePointer;

      fn version(&self) -> Version {
        { self.version }
      }

      fn set_version(&mut self, version: Version) {
        self.version = version;
      }

      impl WithVersion for VersionedNode {}

      node_pointer!(VersionedNode {
        version = MIN_VERSION;

        {
          fn version(&self) -> Version {
            { self.version }
          }
        }
      });
    }
  }
);

/// A fast, lock-free, thread-safe ARENA based `SkipMap` that supports multiple versions, forward and backward iteration.
///
/// If you want to use in non-concurrent environment, you can use [`unsync::versioned::SkipMap`].
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
