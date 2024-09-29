use super::*;

#[cfg(any(all(test, not(miri)), all_tests, test_unsync_trailed,))]
mod tests {
  use super::*;

  __container_tests!("unsync_trailed_map": SkipMap);

  __trailed_map_tests!("unsync_trailed_map": SkipMap<u64>);
}

type Allocator<T> = GenericAllocator<Meta, TrailedNode<T>, Arena>;
type SkipList<T, C> = base::SkipList<Allocator<T>, C>;

node!(
  /// A node that supports only supports trailer.
  struct TrailedNode<T> {
    trailer: ::core::marker::PhantomData<T> = ::core::marker::PhantomData;

    {
      type Link = Link;
      type Trailer = T;
      type ValuePointer = UnsyncValuePointer;
      type Pointer = NodePointer<T>;

      fn set_version(&mut self, version: Version) {

      }

      impl<T: Trailer> WithTrailer for TrailedNode<T> {}

      node_pointer!(TrailedNode<T> {{
        fn version(&self) -> Version {
          MIN_VERSION
        }
      }});
    }
  }
);

/// A fast, ARENA based `SkipMap` that supports trailed structure, forward and backward iteration.
///
/// If you want to use in concurrent environment, you can use [`sync::trailed::SkipMap`].
#[repr(transparent)]
pub struct SkipMap<T: Trailer = (), C = Ascend>(SkipList<T, C>);

impl<T: Trailer, C: Clone> Clone for SkipMap<T, C> {
  #[inline]
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<T: Trailer, C> From<SkipList<T, C>> for SkipMap<T, C> {
  #[inline]
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
