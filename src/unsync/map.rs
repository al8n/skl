use super::*;

#[cfg(any(all(test, not(miri)), all_tests, test_unsync_map,))]
mod tests {
  use super::*;

  __container_tests!("unsync_map": SkipMap<[u8], [u8]>);

  __map_tests!("unsync_map": SkipMap<[u8], [u8]>);
}

type Allocator = GenericAllocator<Meta, RawNode, Arena>;
type SkipList<K, V> = base::SkipList<K, V, Allocator>;

/// Iterator over the [`SkipMap`].
pub type Iter<'a, K, V> = crate::iter::Iter<'a, K, V, Allocator>;

/// Iterator over a subset of the [`SkipMap`].
pub type Range<'a, K, V, Q, R> = crate::iter::Iter<'a, K, V, Allocator, Q, R>;

/// The entry reference of the [`SkipMap`].
pub type Entry<'a, K, V> = crate::EntryRef<'a, K, V, Allocator>;

/// Iterator over the [`SkipMap`].
pub type AllVersionsIter<'a, K, V> = crate::iter::AllVersionsIter<'a, K, V, Allocator>;

/// Iterator over a subset of the [`SkipMap`].
pub type AllVersionsRange<'a, K, V, Q, R> = crate::iter::AllVersionsIter<'a, K, V, Allocator, Q, R>;

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
