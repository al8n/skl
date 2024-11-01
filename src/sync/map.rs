use super::*;

#[cfg(any(all(test, not(miri)), all_tests, test_sync_map,))]
mod tests {
  use super::*;

  __map_tests!("sync_map": SkipMap<[u8], [u8]>);
}

#[cfg(any(all(test, not(miri)), all_tests, test_sync_map_concurrent,))]
mod concurrent_tests {
  use super::*;

  __map_tests!(go "sync_map_map": SkipMap<[u8], [u8]> => crate::tests::TEST_OPTIONS);
}

#[cfg(any(
  all(test, not(miri)),
  all_tests,
  test_sync_map_concurrent_with_optimistic_freelist,
))]
mod concurrent_tests_with_optimistic_freelist {
  use super::*;

  __map_tests!(go "sync_map_map": SkipMap<[u8], [u8]> => crate::tests::TEST_OPTIONS_WITH_OPTIMISTIC_FREELIST);
}

#[cfg(any(
  all(test, not(miri)),
  all_tests,
  test_sync_map_concurrent_with_pessimistic_freelist,
))]
mod concurrent_tests_with_pessimistic_freelist {
  use super::*;

  __map_tests!(go "sync_map_map": SkipMap<[u8], [u8]> => crate::tests::TEST_OPTIONS_WITH_PESSIMISTIC_FREELIST);
}

type Allocator = GenericAllocator<Meta, RawNode, Arena>;
type SkipList<K, V> = base::SkipList<K, V, Allocator>;

/// Iterator over the [`SkipMap`].
pub type Iter<'a, K, V> = crate::iter::Iter<'a, K, V, Allocator>;

/// Iterator over a subset of the [`SkipMap`].
pub type Range<'a, K, V, Q, R> = crate::iter::Iter<'a, K, V, Allocator, Q, R>;

/// Iterator over the [`SkipMap`].
pub type AllVersionsIter<'a, K, V> = crate::iter::AllVersionsIter<'a, K, V, Allocator>;

/// Iterator over a subset of the [`SkipMap`].
pub type AllVersionsRange<'a, K, V, Q, R> = crate::iter::AllVersionsIter<'a, K, V, Allocator, Q, R>;

/// The entry reference of the [`SkipMap`].
pub type Entry<'a, K, V> = crate::EntryRef<'a, K, V, Allocator>;

node!(
  /// A raw node that does not support version and trailer.
  struct RawNode {{
    type Link = Link;

    type ValuePointer = AtomicValuePointer;
    type Pointer = NodePointer;

    fn set_version(&mut self, version: Version) {}

    impl WithoutVersion for RawNode {}

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
pub struct SkipMap<K: ?Sized, V: ?Sized>(SkipList<K, V>);

impl<K: ?Sized, V: ?Sized> Clone for SkipMap<K, V> {
  #[inline]
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<K: ?Sized, V: ?Sized> From<SkipList<K, V>> for SkipMap<K, V> {
  #[inline]
  fn from(list: SkipList<K, V>) -> Self {
    Self(list)
  }
}

impl<K: ?Sized + 'static, V: ?Sized + 'static> crate::traits::List<K, V> for SkipMap<K, V> {
  type Allocator = Allocator;

  #[inline]
  fn as_ref(&self) -> &SkipList<K, V> {
    &self.0
  }

  #[inline]
  fn as_mut(&mut self) -> &mut SkipList<K, V> {
    &mut self.0
  }
}
