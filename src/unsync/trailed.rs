use super::*;

#[cfg(any(all(test, not(miri)), all_tests, test_unsync_trailed,))]
mod tests {
  use super::*;

  __container_tests!("unsync_trailed_map": SkipMap<[u8], [u8]>);

  __trailed_map_tests!("unsync_trailed_map": SkipMap<[u8], [u8], u64>);
}

type Allocator<T> = GenericAllocator<Meta, TrailedNode<T>, Arena>;
type SkipList<K, V, T> = base::SkipList<K, V, Allocator<T>>;

/// Iterator over the [`SkipMap`].
pub type Iter<'a, K, V, T> = crate::iter::Iter<'a, K, V, Allocator<T>>;

/// Iterator over a subset of the [`SkipMap`].
pub type Range<'a, K, V, T, Q, R> = crate::iter::Iter<'a, K, V, Allocator<T>, Q, R>;

/// Iterator over the [`SkipMap`].
pub type AllVersionsIter<'a, K, V, T> = crate::iter::AllVersionsIter<'a, K, V, Allocator<T>>;

/// Iterator over a subset of the [`SkipMap`].
pub type AllVersionsRange<'a, K, V, T, Q, R> =
  crate::iter::AllVersionsIter<'a, K, V, Allocator<T>, Q, R>;

/// The entry reference of the [`SkipMap`].
pub type Entry<'a, K, V, T> = crate::EntryRef<'a, K, V, Allocator<T>>;

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
