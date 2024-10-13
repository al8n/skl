use super::*;

#[cfg(any(all(test, not(miri)), all_tests, test_sync_map,))]
mod tests {
  use super::*;

  __container_tests!("sync_map": SkipMap);

  __map_tests!("sync_map": SkipMap);
}

#[cfg(any(all(test, not(miri)), all_tests, test_sync_map_concurrent,))]
mod concurrent_tests {
  use super::*;

  __map_tests!(go "sync_map_map": SkipMap => crate::tests::TEST_OPTIONS);
}

#[cfg(any(
  all(test, not(miri)),
  all_tests,
  test_sync_map_concurrent_with_optimistic_freelist,
))]
mod concurrent_tests_with_optimistic_freelist {
  use super::*;

  __map_tests!(go "sync_map_map": SkipMap => crate::tests::TEST_OPTIONS_WITH_OPTIMISTIC_FREELIST);
}

#[cfg(any(
  all(test, not(miri)),
  all_tests,
  test_sync_map_concurrent_with_pessimistic_freelist,
))]
mod concurrent_tests_with_pessimistic_freelist {
  use super::*;

  __map_tests!(go "sync_map_map": SkipMap => crate::tests::TEST_OPTIONS_WITH_PESSIMISTIC_FREELIST);
}

type Allocator = GenericAllocator<Meta, RawNode, Arena>;
type SkipList<C> = base::SkipList<Allocator, C>;

/// Iterator over the [`SkipMap`].
pub type Iter<'a, C = Ascend> = crate::iter::Iter<'a, Allocator, C>;

/// Iterator over a subset of the [`SkipMap`].
pub type Range<'a, Q, R, C = Ascend> = crate::iter::Iter<'a, Allocator, C, Q, R>;

/// The entry reference of the [`SkipMap`].
pub type Entry<'a> = crate::EntryRef<'a, Allocator>;

node!(
  /// A raw node that does not support version and trailer.
  struct RawNode {{
    type Link = Link;
    type Trailer = ();
    type ValuePointer = AtomicValuePointer;
    type Pointer = NodePointer;

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
