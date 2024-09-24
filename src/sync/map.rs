use super::*;

#[cfg(any(all(test, not(miri)), all_tests, test_sync_map,))]
mod tests {
  use super::*;

  __container_tests!("sync_map": SkipMap);

  __map_tests!("sync_map": SkipMap);
  __map_tests!(go "sync_map": SkipMap);
}

#[cfg(any(all(test, not(miri)), all_tests, test_sync_map_concurrent,))]
mod concurrent_tests {
  use super::*;

  __map_tests!(go "sync_map": SkipMap);
}

type Allocator = GenericAllocator<Meta, RawNode, Arena>;
type SkipList<C> = base::SkipList<Allocator, C>;

node!(
  /// A raw node that does not support version and trailer.
  struct RawNode {{
    type Link = Link;
    type Trailer = ();
    type ValuePointer = AtomicValuePointer;
    type Pointer = NodePointer;

    fn version(&self) -> Version {
      MIN_VERSION
    }

    fn set_version(&mut self, version: Version) {}

    node_pointer!(RawNode {{
      fn version(&self) -> Version {
        MIN_VERSION
      }
    }});
  }}
);

/// A fast, lock-free, thread-safe ARENA based `SkipMap` that supports forward and backward iteration.
///
/// If you want to use in non-concurrent environment, you can use [`unsync::map::SkipMap`].
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
