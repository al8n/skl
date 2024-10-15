use super::*;

#[cfg(any(all(test, not(miri)), all_tests, test_unsync_full,))]
mod tests {
  use super::*;

  __container_tests!("unsync_full_map": SkipMap);

  __full_map_tests!("unsync_full_map": SkipMap<u64, Ascend>);
}

type Allocator<T> = GenericAllocator<VersionedMeta, FullNode<T>, Arena>;
type SkipList<K, V, T> = generic::SkipList<K, V, Allocator<T>>;

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
      type ValuePointer = UnsyncValuePointer;
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

/// A fast, ARENA based `SkipMap` that supports trailed structure, multiple versions, forward and backward iteration.
///
/// If you want to use in concurrent environment, you can use [`sync::full::SkipMap`].
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
