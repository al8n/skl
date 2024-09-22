use crate::{
  allocator::{WithTrailer, WithVersion},
  full::FullMap,
};

use super::*;

#[macro_export]
macro_rules! full_map_tests {
  ($prefix:literal: $ty:ty) => {
    #[test]
    fn test_basic() {
      $crate::tests::full::basic(
        $crate::Builder::new()
          .with_options($crate::tests::TEST_OPTIONS)
          .alloc::<$ty>()
          .unwrap(),
      );
    }

    #[test]
    fn test_basic_unify() {
      $crate::tests::full::basic(
        $crate::Builder::new()
          .with_options($crate::tests::TEST_OPTIONS)
          .with_unify(true)
          .alloc::<$ty>()
          .unwrap(),
      );
    }

    #[test]
    #[cfg(feature = "memmap")]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::macro_metavars_in_unsafe)]
    fn test_basic_map_mut() {
      unsafe {
        let dir = tempfile::tempdir().unwrap();
        let p = dir
          .path()
          .join(std::format!("test_{}_skipmap_basic_map_mut", $prefix));
        $crate::tests::full::basic(
          $crate::Builder::new()
            .with_options($crate::tests::TEST_OPTIONS)
            .with_create_new(true)
            .with_read(true)
            .with_write(true)
            .map_mut::<$ty, _>(p)
            .unwrap(),
        );
      }
    }

    #[test]
    #[cfg(feature = "memmap")]
    fn test_basic_map_anon() {
      $crate::tests::full::basic(
        $crate::Builder::new()
          .with_options($crate::tests::TEST_OPTIONS)
          .map_anon::<$ty>()
          .unwrap(),
      );
    }

    #[test]
    #[cfg(feature = "memmap")]
    fn test_basic_map_anon_unify() {
      $crate::tests::full::basic(
        $crate::Builder::new()
          .with_options($crate::tests::TEST_OPTIONS)
          .with_unify(true)
          .map_anon::<$ty>()
          .unwrap(),
      );
    }
  };
}

pub(crate) fn basic<M>(mut l: M)
where
  M: FullMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion + WithTrailer,
  <M::Allocator as Sealed>::Trailer: Default,
{
  // Try adding values.
  l.get_or_insert(0, b"key1", &make_value(1), Default::default())
    .unwrap();
  l.get_or_insert(0, b"key3", &make_value(3), Default::default())
    .unwrap();
  l.get_or_insert(0, b"key2", &make_value(2), Default::default())
    .unwrap();

  {
    let mut it = l.iter_all_versions(0);
    let ent = it.seek_lower_bound(Bound::Included(b"key1")).unwrap();
    assert_eq!(ent.key(), b"key1");
    assert_eq!(ent.value().unwrap(), &make_value(1));
    assert_eq!(ent.version(), 0);

    let ent = it.seek_lower_bound(Bound::Included(b"key2")).unwrap();
    assert_eq!(ent.key(), b"key2");
    assert_eq!(ent.value().unwrap(), &make_value(2));
    assert_eq!(ent.version(), 0);

    let ent = it.seek_lower_bound(Bound::Included(b"key3")).unwrap();
    assert_eq!(ent.key(), b"key3");
    assert_eq!(ent.value().unwrap(), &make_value(3));
    assert_eq!(ent.version(), 0);
  }

  l.get_or_insert(1, "a".as_bytes(), &[], Default::default())
    .unwrap();
  l.get_or_insert(2, "a".as_bytes(), &[], Default::default())
    .unwrap();

  {
    let mut it = l.iter_all_versions(2);
    let ent = it.seek_lower_bound(Bound::Included(b"a")).unwrap();
    assert_eq!(ent.key(), b"a");
    assert_eq!(ent.value().unwrap(), &[]);
    assert_eq!(ent.version(), 2);

    let ent = it.next().unwrap();
    assert_eq!(ent.key(), b"a");
    assert_eq!(ent.value().unwrap(), &[]);
    assert_eq!(ent.version(), 1);
  }

  l.get_or_insert(2, "b".as_bytes(), &[], Default::default())
    .unwrap();
  l.get_or_insert(1, "b".as_bytes(), &[], Default::default())
    .unwrap();

  {
    let mut it = l.iter_all_versions(2);
    let ent = it.seek_lower_bound(Bound::Included(b"b")).unwrap();
    assert_eq!(ent.key(), b"b");
    assert_eq!(ent.value().unwrap(), &[]);
    assert_eq!(ent.version(), 2);

    let ent = it.next().unwrap();
    assert_eq!(ent.key(), b"b");
    assert_eq!(ent.value().unwrap(), &[]);
    assert_eq!(ent.version(), 1);

    let ent = it.entry().unwrap();
    assert_eq!(ent.key(), b"b");
    assert_eq!(ent.value().unwrap(), &[]);
    assert_eq!(ent.version(), 1);
  }

  l.get_or_insert(2, b"b", &[], Default::default())
    .unwrap()
    .unwrap();

  assert!(l
    .get_or_insert(2, b"c", &[], Default::default())
    .unwrap()
    .is_none());

  unsafe {
    l.clear().unwrap();
  }

  let l = l.clone();
  {
    let mut it = l.iter_all_versions(0);
    assert!(it.seek_lower_bound(Bound::Unbounded).is_none());
    assert!(it.seek_upper_bound(Bound::Unbounded).is_none());
  }
  assert!(l.is_empty());

  #[cfg(feature = "memmap")]
  l.flush().unwrap();

  #[cfg(feature = "memmap")]
  l.flush_async().unwrap();
}
