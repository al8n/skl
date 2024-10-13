use super::*;

#[cfg(any(all(test, not(miri)), all_tests, test_unsync_versioned,))]
mod tests {
  use super::*;

  __container_tests!("unsync_versioned_map": SkipMap);

  __versioned_map_tests!("unsync_versioned_map": SkipMap<Ascend>);
}

type Allocator = GenericAllocator<VersionedMeta, VersionedNode, Arena>;
type SkipList<C> = base::SkipList<Allocator, C>;

/// Iterator over the [`SkipMap`].
pub type Iter<'a, C = Ascend> = crate::iter::Iter<'a, Allocator, C>;

/// Iterator over a subset of the [`SkipMap`].
pub type Range<'a, Q, R, C = Ascend> = crate::iter::Iter<'a, Allocator, C, Q, R>;

/// The entry reference of the [`SkipMap`].
pub type Entry<'a> = crate::EntryRef<'a, Allocator>;

/// The versioned entry reference of the [`SkipMap`].
pub type VersionedEntry<'a> = crate::VersionedEntryRef<'a, Allocator>;

node!(
  /// A node that only supports version.
  struct VersionedNode {
    version: u64 = MIN_VERSION;

    {
      type Link = Link;
      type Trailer = ();
      type ValuePointer = UnsyncValuePointer;
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
