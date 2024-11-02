use super::*;

#[cfg(any(all(test, not(miri)), all_tests, test_sync_versioned,))]
mod tests {
  crate::__multiple_version_map_tests!("sync_multiple_version_map": super::SkipMap<[u8], [u8]>);
}

#[cfg(any(all(test, not(miri)), all_tests, test_sync_multiple_version_concurrent,))]
mod concurrent_tests {
  crate::__multiple_version_map_tests!(go "sync_multiple_version_map": super::SkipMap<[u8], [u8]> => crate::tests::TEST_OPTIONS);
}

#[cfg(any(
  all(test, not(miri)),
  all_tests,
  test_sync_multiple_version_concurrent_with_optimistic_freelist,
))]
mod concurrent_tests_with_optimistic_freelist {
  crate::__multiple_version_map_tests!(go "sync_multiple_version_map": super::SkipMap<[u8], [u8]> => crate::tests::TEST_OPTIONS_WITH_OPTIMISTIC_FREELIST);
}

#[cfg(any(
  all(test, not(miri)),
  all_tests,
  test_sync_multiple_version_concurrent_with_pessimistic_freelist,
))]
mod concurrent_tests_with_pessimistic_freelist {
  crate::__multiple_version_map_tests!(go "sync_multiple_version_map": super::SkipMap<[u8], [u8]> => crate::tests::TEST_OPTIONS_WITH_PESSIMISTIC_FREELIST);
}

type Allocator = GenericAllocator<VersionedMeta, VersionedNode, Arena>;
type SkipList<K, V> = crate::base::SkipList<K, V, Allocator>;

/// Iterator over the [`SkipMap`].
pub type Iter<'a, K, V> = crate::iter::Iter<'a, K, V, Allocator>;

/// Iterator over a subset of the [`SkipMap`].
pub type Range<'a, K, V, Q, R> = crate::iter::Iter<'a, K, V, Allocator, Q, R>;

/// Iterator over the [`SkipMap`].
pub type IterAll<'a, K, V> = crate::iter::IterAll<'a, K, V, Allocator>;

/// Iterator over a subset of the [`SkipMap`].
pub type RangeAll<'a, K, V, Q, R> = crate::iter::IterAll<'a, K, V, Allocator, Q, R>;

/// The entry reference of the [`SkipMap`].
pub type Entry<'a, K, V> = crate::EntryRef<'a, K, V, Allocator>;

/// The versioned entry reference of the [`SkipMap`].
pub type VersionedEntry<'a, K, V> = crate::VersionedEntryRef<'a, K, V, Allocator>;

node!(
  /// A node that supports version.
  struct VersionedNode {
    flags = Flags::MULTIPLE_VERSION;
    version: u64 = MIN_VERSION;

    {
      type Link = Link;

      type ValuePointer = AtomicValuePointer;
      type Pointer = NodePointer;

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
/// If you want to use in non-concurrent environment, you can use [`multiple_version::unsync::SkipMap`](crate::multiple_version::unsync::SkipMap).
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
