use super::*;

#[cfg(any(all(test, not(miri)), all_tests, test_sync_trailed,))]
mod tests {
  use super::*;

  __container_tests!("sync_trailed_map": SkipMap);

  __trailed_map_tests!("sync_trailed_map": SkipMap<u64>);
}

#[cfg(any(all(test, not(miri)), all_tests, test_sync_trailed_concurrent,))]
mod concurrent_tests {
  use super::*;

  __trailed_map_tests!(go "sync_trailed_map": SkipMap<u64> => crate::tests::TEST_OPTIONS);
}

#[cfg(any(
  all(test, not(miri)),
  all_tests,
  test_sync_trailed_concurrent_with_optimistic_freelist,
))]
mod concurrent_tests_with_optimistic_freelist {
  use super::*;

  __trailed_map_tests!(go "sync_trailed_map": SkipMap<u64> => crate::tests::TEST_OPTIONS_WITH_OPTIMISTIC_FREELIST);
}

#[cfg(any(
  all(test, not(miri)),
  all_tests,
  test_sync_trailed_concurrent_with_pessimistic_freelist,
))]
mod concurrent_tests_with_pessimistic_freelist {
  use super::*;

  __trailed_map_tests!(go "sync_trailed_map": SkipMap<u64> => crate::tests::TEST_OPTIONS_WITH_PESSIMISTIC_FREELIST);
}

type Allocator<T> = GenericAllocator<Meta, TrailedNode<T>, Arena>;
type SkipList<K, V, T> = generic::SkipList<K, V, Allocator<T>>;

/// Iterator over the [`SkipMap`].
pub type Iter<'a, K, V, T> = crate::iter::Iter<'a, K, V, Allocator<T>>;

/// Iterator over a subset of the [`SkipMap`].
pub type Range<'a, K, V, T, Q, R> = crate::iter::Iter<'a, K, V, Allocator<T>, Q, R>;

/// The entry reference of the [`SkipMap`].
pub type Entry<'a, K, V, T> = crate::EntryRef<'a, K, V, Allocator<T>>;

node!(
  /// A node that supports both trailer.
  struct TrailedNode<T> {
    trailer: ::core::marker::PhantomData<T> = ::core::marker::PhantomData;

    {
      type Link = Link;
      type Trailer = T;
      type ValuePointer = AtomicValuePointer;
      type Pointer = NodePointer<T>;

      fn set_version(&mut self, version: Version) {}

      impl<T: Trailer> WithTrailer for TrailedNode<T> {}

      node_pointer!(TrailedNode<T> {{
        fn version(&self) -> Version {
          MIN_VERSION
        }
      }});
    }
  }
);

/// A fast, lock-free, thread-safe ARENA based `SkipMap` that supports trailed structure, forward and backward iteration.
///
/// If you want to use in non-concurrent environment, you can use [`unsync::trailed::SkipMap`].
#[repr(transparent)]
pub struct SkipMap<K: ?Sized, V: ?Sized, T: Trailer = ()>(SkipList<K, V, T>);

impl<K: ?Sized, V: ?Sized, T: Trailer> Clone for SkipMap<K, V, T> {
  #[inline]
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<K: ?Sized, V: ?Sized, T: Trailer> From<SkipList<K, V, T>> for SkipMap<K, V, T> {
  #[inline]
  fn from(list: SkipList<K, V, T>) -> Self {
    Self(list)
  }
}

impl<K: ?Sized + 'static, V: ?Sized + 'static, T: Trailer> crate::traits::List<K, V> for SkipMap<K, V, T> {
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
