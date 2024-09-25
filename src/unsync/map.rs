use super::*;

#[cfg(any(all(test, not(miri)), all_tests, test_unsync_map,))]
mod tests {
  use super::*;

  __container_tests!("unsync_map": SkipMap);

  __map_tests!("unsync_map": SkipMap);
}

type Allocator = GenericAllocator<Meta, RawNode, Arena>;
type SkipList<C> = base::SkipList<Allocator, C>;

node!(
  /// A raw node that does not support version and trailer.
  struct RawNode {{
    type Link = Link;
    type Trailer = ();
    type ValuePointer = UnsyncValuePointer;
    type Pointer = NodePointer<T>;

    fn set_version(&mut self, version: Version) {}

    node_pointer!(RawNode {{
      fn version(&self) -> Version {
         MIN_VERSION
      }
    }});
  }}
);

/// A fast, ARENA based `SkipMap` that supports forward and backward iteration.
///
/// If you want to use in concurrent environment, you can use [`sync::map::SkipMap`].
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
