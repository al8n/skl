use super::*;

#[cfg(any(all(test, not(miri)), all_tests, test_sync_full,))]
mod tests {
  use super::*;

  __container_tests!("sync_full_map": SkipMap<[u8], [u8]>);

  __full_map_tests!("sync_full_map": SkipMap<[u8], [u8], u64>);
}

#[cfg(any(all(test, not(miri)), all_tests, test_sync_full_concurrent,))]
mod concurrent_tests {
  use super::*;

  __full_map_tests!(go "sync_full_map": SkipMap<[u8], [u8], u64> => crate::tests::TEST_OPTIONS);
}

#[cfg(any(
  all(test, not(miri)),
  all_tests,
  test_sync_full_concurrent_with_optimistic_freelist,
))]
mod concurrent_tests_with_optimistic_freelist {
  use super::*;

  __full_map_tests!(go "sync_full_map": SkipMap<[u8], [u8], u64> => crate::tests::TEST_OPTIONS_WITH_OPTIMISTIC_FREELIST);
}

#[cfg(any(
  all(test, not(miri)),
  all_tests,
  test_sync_full_concurrent_with_pessimistic_freelist,
))]
mod concurrent_tests_with_pessimistic_freelist {
  use super::*;

  __full_map_tests!(go "sync_full_map": SkipMap<[u8], [u8], u64> => crate::tests::TEST_OPTIONS_WITH_PESSIMISTIC_FREELIST);
}

type Allocator<T> = GenericAllocator<VersionedMeta, FullNode<T>, Arena>;
type SkipList<K, V, T> = base::SkipList<K, V, Allocator<T>>;

/// Iterator over the [`SkipMap`].
pub type Iter<'a, K, V, T> = crate::iter::Iter<'a, K, V, Allocator<T>>;

/// Iterator over a subset of the [`SkipMap`].
pub type Range<'a, K, V, T, Q, R> = crate::iter::Iter<'a, K, V, Allocator<T>, Q, R>;

/// The entry reference of the [`SkipMap`].
pub type Entry<'a, K, V, T> = crate::EntryRef<'a, K, V, Allocator<T>>;

/// The versioned entry reference of the [`SkipMap`].
pub type VersionedEntry<'a, K, V, T> = crate::VersionedEntryRef<'a, K, V, Allocator<T>>;

node!(
  /// A node that supports both version and trailer.
  struct FullNode<T> {
    version: u64 = MIN_VERSION;
    trailer: ::core::marker::PhantomData<T> = ::core::marker::PhantomData;

    {
      type Link = Link;
      type Trailer = T;
      type ValuePointer = AtomicValuePointer;
      type Pointer = NodePointer<T>;

      fn set_version(&mut self, version: Version) {
        self.version = version;
      }

      impl<T: Trailer> WithVersion for FullNode<T> {}
      impl<T: Trailer> WithTrailer for FullNode<T> {}

      node_pointer!(FullNode<T> {
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

/// A fast, lock-free, thread-safe ARENA based `SkipMap` that supports full structure, multiple versions, forward and backward iteration.
///
/// If you want to use in non-concurrent environment, you can use [`unsync::full::SkipMap`].
#[repr(transparent)]
pub struct SkipMap<K: ?Sized, V: ?Sized, T: Trailer = ()>(pub(super) SkipList<K, V, T>);

impl<K: ?Sized, V: ?Sized, T: Trailer> Clone for SkipMap<K, V, T> {
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<K: ?Sized, V: ?Sized, T: Trailer> From<SkipList<K, V, T>> for SkipMap<K, V, T> {
  fn from(list: SkipList<K, V, T>) -> Self {
    Self(list)
  }
}

impl<K: ?Sized + 'static, V: ?Sized + 'static, T: Trailer> crate::traits::List<K, V>
  for SkipMap<K, V, T>
{
  type Allocator = Allocator<T>;

  #[inline]
  fn as_ref(&self) -> &SkipList<K, V, T> {
    &self.0
  }

  #[inline]
  fn as_mut(&mut self) -> &mut SkipList<K, V, T> {
    &mut self.0
  }
}
