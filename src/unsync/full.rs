use super::*;

#[cfg(any(all(test, not(miri)), all_tests, test_unsync_full,))]
mod tests {
  use super::*;

  __container_tests!("unsync_full_map": SkipMap);

  __full_map_tests!("unsync_full_map": SkipMap<u64, Ascend>);
}

type Allocator<T> = GenericAllocator<VersionedMeta, FullNode<T>, Arena>;
type SkipList<T, C> = base::SkipList<Allocator<T>, C>;

/// Iterator over the [`SkipMap`].
pub type Iter<'a, T, C = Ascend> = crate::iter::Iter<'a, Allocator<T>, C>;

/// Iterator over a subset of the [`SkipMap`].
pub type Range<'a, T, Q, R, C = Ascend> = crate::iter::Iter<'a, Allocator<T>, C, Q, R>;

/// The entry reference of the [`SkipMap`].
pub type Entry<'a, T> = crate::EntryRef<'a, Allocator<T>>;

/// The versioned entry reference of the [`SkipMap`].
pub type VersionedEntry<'a, T> = crate::VersionedEntryRef<'a, Allocator<T>>;

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
pub struct SkipMap<T: Trailer = (), C = Ascend>(pub(super) SkipList<T, C>);

impl<T: Trailer, C> From<SkipList<T, C>> for SkipMap<T, C> {
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

impl<T: Trailer, C: Clone> Clone for SkipMap<T, C> {
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}
