use core::sync::atomic::Ordering;

use dbutils::buffer::VacantBuffer;

use crate::{
  allocator::WithVersion, versioned::VersionedMap, KeyBuilder, ValueBuilder, MIN_VERSION,
};

use super::*;

pub(crate) fn basic<M>(mut l: M)
where
  M: VersionedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  // Try adding values.
  l.get_or_insert(0, b"key1", &make_value(1)).unwrap();
  l.get_or_insert(0, b"key3", &make_value(3)).unwrap();
  l.get_or_insert(0, b"key2", &make_value(2)).unwrap();

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

  l.get_or_insert(1, "a".as_bytes(), &[]).unwrap();
  l.get_or_insert(2, "a".as_bytes(), &[]).unwrap();

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

  l.get_or_insert(2, "b".as_bytes(), &[]).unwrap();
  l.get_or_insert(1, "b".as_bytes(), &[]).unwrap();

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

  l.get_or_insert(2, b"b", &[]).unwrap().unwrap();

  assert!(l.get_or_insert(2, b"c", &[]).unwrap().is_none());

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

pub(crate) fn iter_all_versions_mvcc<M>(l: M)
where
  M: VersionedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  l.get_or_insert(1, b"a", b"a1").unwrap();
  l.get_or_insert(3, b"a", b"a2").unwrap();
  l.get_or_insert(1, b"c", b"c1").unwrap();
  l.get_or_insert(3, b"c", b"c2").unwrap();

  let mut it = l.iter_all_versions(0);
  let mut num = 0;
  while it.next().is_some() {
    num += 1;
  }
  assert_eq!(num, 0);

  let mut it = l.iter_all_versions(1);
  let mut num = 0;
  while it.next().is_some() {
    num += 1;
  }
  assert_eq!(num, 2);

  let mut it = l.iter_all_versions(2);
  let mut num = 0;
  while it.next().is_some() {
    num += 1;
  }
  assert_eq!(num, 2);

  let mut it = l.iter_all_versions(3);
  let mut num = 0;
  while it.next().is_some() {
    num += 1;
  }
  assert_eq!(num, 4);

  let mut it = l.iter_all_versions(0);
  assert!(it.seek_lower_bound(Bound::Unbounded).is_none());
  assert!(it.seek_upper_bound(Bound::Unbounded).is_none());

  let mut it = l.iter_all_versions(1);
  let ent = it.seek_lower_bound(Bound::Unbounded).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value().unwrap(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = it.seek_upper_bound(Bound::Unbounded).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value().unwrap(), b"c1");
  assert_eq!(ent.version(), 1);

  let mut it = l.iter_all_versions(2);
  let ent = it.seek_lower_bound(Bound::Unbounded).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value().unwrap(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = it.seek_upper_bound(Bound::Unbounded).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value().unwrap(), b"c1");
  assert_eq!(ent.version(), 1);

  let mut it = l.iter_all_versions(3);

  let ent = it.seek_upper_bound(Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value().unwrap(), b"a2");
  assert_eq!(ent.version(), 3);

  let ent = it.seek_upper_bound(Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value().unwrap(), b"c2");
  assert_eq!(ent.version(), 3);

  let ent = it.seek_lower_bound(Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value().unwrap(), b"c2");
  assert_eq!(ent.version(), 3);

  let ent = it.seek_lower_bound(Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value().unwrap(), b"c2");
  assert_eq!(ent.version(), 3);
}

pub(crate) fn get_mvcc<M>(l: M)
where
  M: VersionedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  l.get_or_insert(1, b"a", b"a1").unwrap();
  l.get_or_insert(3, b"a", b"a2").unwrap();
  l.get_or_insert(1, b"c", b"c1").unwrap();
  l.get_or_insert(3, b"c", b"c2").unwrap();

  let ent = l.get(1, b"a").unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = l.get(2, b"a").unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = l.get(3, b"a").unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.version(), 3);

  let ent = l.get(4, b"a").unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.version(), 3);

  assert!(l.get(0, b"b").is_none());
  assert!(l.get(1, b"b").is_none());
  assert!(l.get(2, b"b").is_none());
  assert!(l.get(3, b"b").is_none());
  assert!(l.get(4, b"b").is_none());

  let ent = l.get(1, b"c").unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.get(2, b"c").unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.get(3, b"c").unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);

  let ent = l.get(4, b"c").unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);

  assert!(l.get(5, b"d").is_none());
}

pub(crate) fn gt<M>(l: M)
where
  M: VersionedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  l.get_or_insert(1, b"a", b"a1").unwrap();
  l.get_or_insert(3, b"a", b"a2").unwrap();
  l.get_or_insert(1, b"c", b"c1").unwrap();
  l.get_or_insert(3, b"c", b"c2").unwrap();
  l.get_or_insert(5, b"c", b"c3").unwrap();

  assert!(l.lower_bound(0, Bound::Excluded(b"a")).is_none());
  assert!(l.lower_bound(0, Bound::Excluded(b"b")).is_none());
  assert!(l.lower_bound(0, Bound::Excluded(b"c")).is_none());

  let ent = l.lower_bound(1, Bound::Excluded(b"")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(2, Bound::Excluded(b"")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(3, Bound::Excluded(b"")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(1, Bound::Excluded(b"a")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(2, Bound::Excluded(b"a")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(3, Bound::Excluded(b"a")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(1, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(2, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(3, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(4, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(5, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c3");
  assert_eq!(ent.version(), 5);

  let ent = l.lower_bound(6, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c3");
  assert_eq!(ent.version(), 5);

  assert!(l.lower_bound(1, Bound::Excluded(b"c")).is_none());
  assert!(l.lower_bound(2, Bound::Excluded(b"c")).is_none());
  assert!(l.lower_bound(3, Bound::Excluded(b"c")).is_none());
  assert!(l.lower_bound(4, Bound::Excluded(b"c")).is_none());
  assert!(l.lower_bound(5, Bound::Excluded(b"c")).is_none());
  assert!(l.lower_bound(6, Bound::Excluded(b"c")).is_none());
}

pub(crate) fn ge<M>(l: M)
where
  M: VersionedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  l.get_or_insert(1, b"a", b"a1").unwrap();
  l.get_or_insert(3, b"a", b"a2").unwrap();
  l.get_or_insert(1, b"c", b"c1").unwrap();
  l.get_or_insert(3, b"c", b"c2").unwrap();

  assert!(l.lower_bound(MIN_VERSION, Bound::Included(b"a")).is_none());
  assert!(l.lower_bound(MIN_VERSION, Bound::Included(b"b")).is_none());
  assert!(l.lower_bound(MIN_VERSION, Bound::Included(b"c")).is_none());

  let ent = l.lower_bound(1, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(2, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(3, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(4, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(1, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(2, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(3, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(4, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(1, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(2, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(3, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(4, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);

  assert!(l.lower_bound(MIN_VERSION, Bound::Included(b"d")).is_none());
  assert!(l.lower_bound(1, Bound::Included(b"d")).is_none());
  assert!(l.lower_bound(2, Bound::Included(b"d")).is_none());
  assert!(l.lower_bound(3, Bound::Included(b"d")).is_none());
  assert!(l.lower_bound(4, Bound::Included(b"d")).is_none());
}

pub(crate) fn le<M>(l: M)
where
  M: VersionedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  l.get_or_insert(1, b"a", b"a1").unwrap();
  l.get_or_insert(3, b"a", b"a2").unwrap();
  l.get_or_insert(1, b"c", b"c1").unwrap();
  l.get_or_insert(3, b"c", b"c2").unwrap();

  assert!(l.upper_bound(MIN_VERSION, Bound::Included(b"a")).is_none());
  assert!(l.upper_bound(MIN_VERSION, Bound::Included(b"b")).is_none());
  assert!(l.upper_bound(MIN_VERSION, Bound::Included(b"c")).is_none());

  let ent = l.upper_bound(1, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(2, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(3, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(4, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(1, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(2, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(3, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(4, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(1, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(2, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(3, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(4, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(1, Bound::Included(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(2, Bound::Included(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(3, Bound::Included(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(4, Bound::Included(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);
}

pub(crate) fn lt<M>(l: M)
where
  M: VersionedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  l.get_or_insert(1, b"a", b"a1").unwrap();
  l.get_or_insert(3, b"a", b"a2").unwrap();
  l.get_or_insert(1, b"c", b"c1").unwrap();
  l.get_or_insert(3, b"c", b"c2").unwrap();

  assert!(l.upper_bound(MIN_VERSION, Bound::Excluded(b"a")).is_none());
  assert!(l.upper_bound(MIN_VERSION, Bound::Excluded(b"b")).is_none());
  assert!(l.upper_bound(MIN_VERSION, Bound::Excluded(b"c")).is_none());
  assert!(l.upper_bound(1, Bound::Excluded(b"a")).is_none());
  assert!(l.upper_bound(2, Bound::Excluded(b"a")).is_none());

  let ent = l.upper_bound(1, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(2, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(3, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(4, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(1, Bound::Excluded(b"c")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(2, Bound::Excluded(b"c")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(3, Bound::Excluded(b"c")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(4, Bound::Excluded(b"c")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(1, Bound::Excluded(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(2, Bound::Excluded(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(3, Bound::Excluded(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(4, Bound::Excluded(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);
}

#[cfg(not(miri))]
pub(crate) fn basic_large<M>(l: M)
where
  M: VersionedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  let n = 1000;

  for i in 0..n {
    l.get_or_insert(MIN_VERSION, &key(i), &new_value(i))
      .unwrap();
  }

  for i in 0..n {
    let k = key(i);
    let ent = l.get(MIN_VERSION, &k).unwrap();
    assert_eq!(new_value(i), ent.value());
    assert_eq!(ent.version(), 0);
    assert_eq!(ent.key(), k);
  }

  assert_eq!(n, l.len());
}

#[cfg(all(
  feature = "std",
  any(all(test, not(miri)), all_tests, test_sync_versioned,)
))]
pub(crate) fn concurrent_basic<M>(l: M)
where
  M: VersionedMap + Clone + Send + 'static,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  #[cfg(not(miri))]
  const N: usize = 1000;
  #[cfg(miri)]
  const N: usize = 200;

  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      l.get_or_insert(MIN_VERSION, &key(i), &new_value(i))
        .unwrap();
    });
  }
  while l.refs() > 1 {
    ::core::hint::spin_loop();
  }
  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      let k = key(i);
      assert_eq!(
        l.get(MIN_VERSION, &k).unwrap().value(),
        new_value(i),
        "broken: {i}"
      );
    });
  }
  while l.refs() > 1 {
    ::core::hint::spin_loop();
  }
}

#[cfg(all(
  feature = "std",
  any(all(test, not(miri)), all_tests, test_sync_versioned,)
))]
pub(crate) fn concurrent_basic2<M>(l: M)
where
  M: VersionedMap + Clone + Send + 'static,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  #[cfg(not(miri))]
  const N: usize = 1000;
  #[cfg(miri)]
  const N: usize = 200;

  for i in 0..N {
    let l1 = l.clone();
    let l2 = l.clone();
    std::thread::Builder::new()
      .name(format!("versionedmap-concurrent-basic2-writer-{i}-1"))
      .spawn(move || {
        let _ = l1.insert(MIN_VERSION, &key(i), &new_value(i));
      })
      .unwrap();

    std::thread::Builder::new()
      .name(format!("versionedmap-concurrent-basic2-writer{i}-2"))
      .spawn(move || {
        let _ = l2.insert(MIN_VERSION, &key(i), &new_value(i));
      })
      .unwrap();
  }
  while l.refs() > 1 {
    ::core::hint::spin_loop();
  }
  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      let k = key(i);
      assert_eq!(
        l.get(MIN_VERSION, &k).unwrap().value(),
        new_value(i),
        "broken: {i}"
      );
    });
  }
  while l.refs() > 1 {
    ::core::hint::spin_loop();
  }
}

#[cfg(all(
  all(feature = "std", not(miri)),
  any(all(test, not(miri)), all_tests, test_sync_versioned,)
))]
pub(crate) fn concurrent_basic_big_values<M>(l: M)
where
  M: VersionedMap + Clone + Send + 'static,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  #[cfg(not(any(miri, feature = "loom")))]
  const N: usize = 100;
  #[cfg(any(miri, feature = "loom"))]
  const N: usize = 5;

  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      l.get_or_insert(MIN_VERSION, &key(i), &big_value(i))
        .unwrap();
    });
  }
  while l.refs() > 1 {
    ::core::hint::spin_loop();
  }
  // assert_eq!(N, l.len());
  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      let k = key(i);
      assert_eq!(
        l.get(MIN_VERSION, &k).unwrap().value(),
        big_value(i),
        "broken: {i}"
      );
    });
  }
  while l.refs() > 1 {
    ::core::hint::spin_loop();
  }
}

#[cfg(all(
  feature = "std",
  any(all(test, not(miri)), all_tests, test_sync_versioned,)
))]
pub(crate) fn concurrent_one_key<M>(l: M)
where
  M: VersionedMap + Clone + Send + 'static,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  use core::sync::atomic::Ordering;
  use std::sync::Arc;

  #[cfg(not(miri))]
  const N: usize = 1000;
  #[cfg(miri)]
  const N: usize = 200;

  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      let _ = l.get_or_insert(MIN_VERSION, b"thekey", &make_value(i));
    });
  }

  while l.refs() > 1 {
    ::core::hint::spin_loop();
  }

  let saw_value = Arc::new(crate::common::AtomicU32::new(0));
  for _ in 0..N {
    let l = l.clone();
    let saw_value = saw_value.clone();
    std::thread::spawn(move || {
      let ent = l.get(MIN_VERSION, b"thekey").unwrap();
      let val = ent.value();
      let num: usize = core::str::from_utf8(&val[1..]).unwrap().parse().unwrap();
      assert!((0..N).contains(&num));

      let mut it = l.iter_all_versions(MIN_VERSION);
      let ent = it.seek_lower_bound(Bound::Included(b"thekey")).unwrap();
      let val = ent.value().unwrap();
      let num: usize = core::str::from_utf8(&val[1..]).unwrap().parse().unwrap();
      assert!((0..N).contains(&num));
      assert_eq!(ent.key(), b"thekey");
      saw_value.fetch_add(1, Ordering::SeqCst);
    });
  }

  while l.refs() > 1 {
    ::core::hint::spin_loop();
  }

  assert_eq!(N, saw_value.load(Ordering::SeqCst) as usize);
  assert_eq!(l.len(), 1);
}

#[cfg(all(
  feature = "std",
  any(all(test, not(miri)), all_tests, test_sync_versioned,)
))]
pub(crate) fn concurrent_one_key2<M>(l: M)
where
  M: VersionedMap + Clone + Send + 'static,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  use core::sync::atomic::Ordering;
  use std::sync::Arc;

  #[cfg(not(miri))]
  const N: usize = 1000;
  #[cfg(miri)]
  const N: usize = 200;

  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      let _ = l.insert(MIN_VERSION, b"thekey", &make_value(i));
    });
  }

  while l.refs() > 1 {
    ::core::hint::spin_loop();
  }

  let saw_value = Arc::new(crate::common::AtomicU32::new(0));
  for _ in 0..N {
    let l = l.clone();
    let saw_value = saw_value.clone();
    std::thread::spawn(move || {
      let ent = l.get(MIN_VERSION, b"thekey").unwrap();
      let val = ent.value();
      let num: usize = core::str::from_utf8(&val[1..]).unwrap().parse().unwrap();
      assert!((0..N).contains(&num));

      let mut it = l.iter_all_versions(MIN_VERSION);
      let ent = it.seek_lower_bound(Bound::Included(b"thekey")).unwrap();
      let val = ent.value().unwrap();
      let num: usize = core::str::from_utf8(&val[1..]).unwrap().parse().unwrap();
      assert!((0..N).contains(&num));
      assert_eq!(ent.key(), b"thekey");
      saw_value.fetch_add(1, Ordering::SeqCst);
    });
  }

  while l.refs() > 1 {
    ::core::hint::spin_loop();
  }

  assert_eq!(N, saw_value.load(Ordering::SeqCst) as usize);
  assert_eq!(l.len(), 1);
}

pub(crate) fn iter_all_versions_next<M>(l: M)
where
  M: VersionedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  const N: usize = 100;

  for i in (0..N).rev() {
    l.get_or_insert(MIN_VERSION, &make_int_key(i), &make_value(i))
      .unwrap();
  }

  let mut it = l.iter_all_versions(MIN_VERSION);
  let mut ent = it.seek_lower_bound(Bound::Unbounded).unwrap();
  for i in 0..N {
    assert_eq!(ent.key(), make_int_key(i));
    assert_eq!(ent.value().unwrap(), make_value(i));
    if i != N - 1 {
      ent = it.next().unwrap();
    }
  }

  assert!(it.next().is_none());
}

pub(crate) fn range_next<M>(l: M)
where
  M: VersionedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  const N: usize = 100;

  for i in (0..N).rev() {
    l.get_or_insert(MIN_VERSION, &make_int_key(i), &make_value(i))
      .unwrap();
  }

  let upper = make_int_key(50);
  let mut it = l.range(MIN_VERSION, ..=upper.as_slice());
  let mut ent = it.seek_lower_bound(Bound::Unbounded);
  for i in 0..N {
    if i <= 50 {
      {
        let ent = ent.unwrap();
        assert_eq!(ent.key(), make_int_key(i));
        assert_eq!(ent.value(), make_value(i));
      }
      ent = it.next();
    } else {
      assert!(ent.is_none());
      ent = it.next();
    }
  }

  assert!(it.next().is_none());
}

pub(crate) fn iter_all_versions_prev<M>(l: M)
where
  M: VersionedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(MIN_VERSION, &make_int_key(i), &make_value(i))
      .unwrap();
  }

  let mut it = l.iter_all_versions(MIN_VERSION);
  let mut ent = it.seek_upper_bound(Bound::Unbounded).unwrap();
  for i in (0..N).rev() {
    assert_eq!(ent.key(), make_int_key(i));
    assert_eq!(ent.value().unwrap(), make_value(i));
    if i != 0 {
      ent = it.next_back().unwrap();
    }
  }

  assert!(it.next_back().is_none());
}

pub(crate) fn range_prev<M>(l: M)
where
  M: VersionedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(MIN_VERSION, &make_int_key(i), &make_value(i))
      .unwrap();
  }

  let lower = make_int_key(50);
  let mut it = l.range(MIN_VERSION, lower.as_slice()..);
  let mut ent = it.seek_upper_bound(Bound::Unbounded);
  for i in (0..N).rev() {
    if i >= 50 {
      {
        let ent = ent.unwrap();
        assert_eq!(ent.key(), make_int_key(i));
        assert_eq!(ent.value(), make_value(i));
      }
      ent = it.next_back();
    } else {
      assert!(ent.is_none());
      ent = it.next_back();
    }
  }

  assert!(it.next_back().is_none());
}

pub(crate) fn iter_all_versions_seek_ge<M>(l: M)
where
  M: VersionedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  const N: usize = 100;

  for i in (0..N).rev() {
    let v = i * 10 + 1000;
    l.get_or_insert(MIN_VERSION, &make_int_key(v), &make_value(v))
      .unwrap();
  }

  let mut it = l.iter_all_versions(MIN_VERSION);
  let ent = it.seek_lower_bound(Bound::Included(b"")).unwrap();
  assert_eq!(ent.key(), make_int_key(1000));
  assert_eq!(ent.value().unwrap(), make_value(1000));

  let ent = it.seek_lower_bound(Bound::Included(b"01000")).unwrap();
  assert_eq!(ent.key(), make_int_key(1000));
  assert_eq!(ent.value().unwrap(), make_value(1000));

  let ent = it.seek_lower_bound(Bound::Included(b"01005")).unwrap();
  assert_eq!(ent.key(), make_int_key(1010));
  assert_eq!(ent.value().unwrap(), make_value(1010));

  let ent = it.seek_lower_bound(Bound::Included(b"01010")).unwrap();
  assert_eq!(ent.key(), make_int_key(1010));
  assert_eq!(ent.value().unwrap(), make_value(1010));

  let ent = it.seek_lower_bound(Bound::Included(b"01020")).unwrap();
  assert_eq!(ent.key(), make_int_key(1020));
  assert_eq!(ent.value().unwrap(), make_value(1020));

  let ent = it.seek_lower_bound(Bound::Included(b"01200")).unwrap();
  assert_eq!(ent.key(), make_int_key(1200));
  assert_eq!(ent.value().unwrap(), make_value(1200));

  let ent = it.seek_lower_bound(Bound::Included(b"01100")).unwrap();
  assert_eq!(ent.key(), make_int_key(1100));
  assert_eq!(ent.value().unwrap(), make_value(1100));

  let ent = it.seek_lower_bound(Bound::Included(b"99999"));
  assert!(ent.is_none());

  l.get_or_insert(MIN_VERSION, &[], &[]).unwrap();
  let ent = it.seek_lower_bound(Bound::Included(b"")).unwrap();
  assert_eq!(ent.key(), &[]);
  assert_eq!(ent.value().unwrap(), &[]);

  let ent = it.seek_lower_bound(Bound::Included(b"")).unwrap();
  assert_eq!(ent.key(), &[]);
  assert_eq!(ent.value().unwrap(), &[]);
}

pub(crate) fn iter_all_versions_seek_lt<M>(l: M)
where
  M: VersionedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  const N: usize = 100;

  for i in (0..N).rev() {
    let v = i * 10 + 1000;
    l.get_or_insert(MIN_VERSION, &make_int_key(v), &make_value(v))
      .unwrap();
  }

  let mut it = l.iter_all_versions(MIN_VERSION);
  assert!(it.seek_upper_bound(Bound::Excluded(b"")).is_none());

  let ent = it.seek_upper_bound(Bound::Excluded(b"01000"));
  assert!(ent.is_none());

  let ent = it.seek_upper_bound(Bound::Excluded(b"01001")).unwrap();
  assert_eq!(ent.key(), make_int_key(1000));
  assert_eq!(ent.value().unwrap(), make_value(1000));

  let ent = it.seek_upper_bound(Bound::Excluded(b"01991")).unwrap();
  assert_eq!(ent.key(), make_int_key(1990));
  assert_eq!(ent.value().unwrap(), make_value(1990));

  let ent = it.seek_upper_bound(Bound::Excluded(b"99999")).unwrap();
  assert_eq!(ent.key(), make_int_key(1990));
  assert_eq!(ent.value().unwrap(), make_value(1990));

  l.get_or_insert(MIN_VERSION, &[], &[]).unwrap();
  assert!(l.as_ref().lt(MIN_VERSION, &[], false).is_none());

  let ent = it.seek_upper_bound(Bound::Excluded(b""));
  assert!(ent.is_none());

  let ent = it.seek_upper_bound(Bound::Excluded(b"\x01")).unwrap();
  assert_eq!(ent.key(), &[]);
  assert_eq!(ent.value().unwrap(), &[]);
}

pub(crate) fn range<M>(l: M)
where
  M: VersionedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  for i in 1..10 {
    l.get_or_insert(MIN_VERSION, &make_int_key(i), &make_value(i))
      .unwrap();
  }

  let k3 = make_int_key(3);
  let k7 = make_int_key(7);
  let mut it = l.range(MIN_VERSION, k3.as_slice()..k7.as_slice()).clone();
  assert_eq!(it.bounds(), &(k3.as_slice()..k7.as_slice()));

  for i in 3..=6 {
    let k = make_int_key(i);
    let ent = it.seek_lower_bound(Bound::Included(&k)).unwrap();
    assert_eq!(ent.key(), make_int_key(i));
    assert_eq!(ent.value(), make_value(i));
  }

  for i in 1..3 {
    let k = make_int_key(i);
    let ent = it.seek_lower_bound(Bound::Included(&k)).unwrap();
    assert_eq!(ent.key(), make_int_key(3));
    assert_eq!(ent.value(), make_value(3));
  }

  for i in 7..10 {
    let k = make_int_key(i);
    assert!(it.seek_lower_bound(Bound::Included(&k)).is_none());
  }

  for i in 7..10 {
    let k = make_int_key(i);
    let ent = it.seek_upper_bound(Bound::Included(&k)).unwrap();
    assert_eq!(ent.key(), make_int_key(6));
    assert_eq!(ent.value(), make_value(6));
  }

  let ent = it
    .seek_lower_bound(Bound::Included(&make_int_key(6)))
    .unwrap();
  assert_eq!(ent.key(), make_int_key(6));
  assert_eq!(ent.value(), make_value(6));

  assert!(it.next().is_none());

  let ent = it
    .seek_upper_bound(Bound::Included(&make_int_key(6)))
    .unwrap();
  assert_eq!(ent.key(), make_int_key(6));
  assert_eq!(ent.value(), make_value(6));

  assert!(it.next().is_none());

  for i in 4..=7 {
    let k = make_int_key(i);
    let ent = it.seek_upper_bound(Bound::Excluded(&k)).unwrap();
    assert_eq!(ent.key(), make_int_key(i - 1));
    assert_eq!(ent.value(), make_value(i - 1));
  }

  for i in 7..10 {
    let k = make_int_key(i);
    let ent = it.seek_upper_bound(Bound::Excluded(&k)).unwrap();
    assert_eq!(ent.key(), make_int_key(6));
    assert_eq!(ent.value(), make_value(6));
  }

  for i in 1..3 {
    let k = make_int_key(i);
    let ent = it.seek_lower_bound(Bound::Excluded(&k)).unwrap();
    assert_eq!(ent.key(), make_int_key(3));
    assert_eq!(ent.value(), make_value(3));
  }

  for i in 1..4 {
    let k = make_int_key(i);
    assert!(it.seek_upper_bound(Bound::Excluded(&k)).is_none());
  }

  let ent = it
    .seek_upper_bound(Bound::Excluded(&make_int_key(4)))
    .unwrap();
  assert_eq!(ent.key(), make_int_key(3));
  assert_eq!(ent.value(), make_value(3));

  assert!(it.next_back().is_none());
}

pub(crate) fn iter_latest<M>(l: M)
where
  M: VersionedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(MIN_VERSION, &make_int_key(i), &make_value(i))
      .unwrap();
  }

  for i in 50..N {
    l.get_or_insert(1, &make_int_key(i), &make_value(i + 1000))
      .unwrap();
  }

  for i in 0..50 {
    l.get_or_insert(2, &make_int_key(i), &make_value(i + 1000))
      .unwrap();
  }

  let mut it = l.iter(4);
  let mut num = 0;
  for i in 0..N {
    let ent = it.next().unwrap();
    assert_eq!(ent.key(), make_int_key(i));
    assert_eq!(ent.value(), make_value(i + 1000));

    num += 1;
  }
  assert_eq!(num, N);
}

pub(crate) fn range_latest<M>(l: M)
where
  M: VersionedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(MIN_VERSION, &make_int_key(i), &make_value(i))
      .unwrap();
  }

  for i in 50..N {
    l.get_or_insert(1, &make_int_key(i), &make_value(i + 1000))
      .unwrap();
  }

  for i in 0..50 {
    l.get_or_insert(2, &make_int_key(i), &make_value(i + 1000))
      .unwrap();
  }

  let mut it = l.range::<[u8], _>(4, ..);
  let mut num = 0;
  for i in 0..N {
    let ent = it.next().unwrap();
    assert_eq!(ent.key(), make_int_key(i));
    assert_eq!(ent.value(), make_value(i + 1000));

    num += 1;
  }
  assert_eq!(num, N);
}

#[cfg(feature = "memmap")]
pub(crate) fn reopen_mmap<M>(prefix: &str)
where
  M: VersionedMap<Comparator = dbutils::Ascend> + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  use crate::Builder;

  unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join(std::format!("{prefix}_reopen_skipmap"));
    {
      let l = Builder::new()
        .with_create_new(true)
        .with_read(true)
        .with_write(true)
        .with_capacity(ARENA_SIZE as u32)
        .map_mut::<M, _>(&p)
        .unwrap();
      for i in 0..1000 {
        l.get_or_insert(MIN_VERSION, &key(i), &new_value(i))
          .unwrap();
      }
      l.flush().unwrap();
    }

    let l = Builder::new()
      .with_read(true)
      .with_write(true)
      .with_capacity(ARENA_SIZE as u32)
      .map::<M, _>(&p)
      .unwrap();
    assert_eq!(1000, l.len());
    for i in 0..1000 {
      let k = key(i);
      let ent = l.get(MIN_VERSION, &k).unwrap();
      assert_eq!(new_value(i), ent.value());
      assert_eq!(ent.version(), 0);
      assert_eq!(ent.key(), k);
    }
  }
}

#[cfg(feature = "memmap")]
pub(crate) fn reopen_mmap2<M>(prefix: &str)
where
  M: VersionedMap<Comparator = dbutils::Ascend> + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  use crate::Builder;

  unsafe {
    use rand::seq::SliceRandom;

    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join(::std::format!("{prefix}_reopen2_skipmap"));
    {
      let l = Builder::new()
        .with_create_new(true)
        .with_read(true)
        .with_write(true)
        .with_capacity(ARENA_SIZE as u32)
        .map_mut::<M, _>(&p)
        .unwrap();
      let mut data = (0..1000).collect::<::std::vec::Vec<usize>>();
      data.shuffle(&mut rand::thread_rng());
      for i in &data {
        let i = *i;
        l.get_or_insert(i as u64, &key(i), &new_value(i)).unwrap();
      }
      l.flush_async().unwrap();
      assert_eq!(l.max_version(), 999);
      assert_eq!(l.min_version(), 0);

      for i in data {
        let k = key(i);
        let ent = l.get(i as u64, &k).unwrap();
        assert_eq!(new_value(i), ent.value());
        assert_eq!(ent.version(), i as u64);
        assert_eq!(ent.key(), k);
      }
    }

    let l = Builder::new()
      .with_read(true)
      .with_write(true)
      .with_capacity(ARENA_SIZE as u32)
      .map::<M, _>(&p)
      .unwrap();
    assert_eq!(1000, l.len());
    let mut data = (0..1000).collect::<::std::vec::Vec<usize>>();
    data.shuffle(&mut rand::thread_rng());
    for i in data {
      let k = key(i);
      let ent = l.get(i as u64, &k).unwrap();
      assert_eq!(new_value(i), ent.value());
      assert_eq!(ent.version(), i as u64);
      assert_eq!(ent.key(), k);
    }
    assert_eq!(l.max_version(), 999);
    assert_eq!(l.min_version(), 0);
  }
}

#[cfg(feature = "memmap")]
pub(crate) fn reopen_mmap3<M>(prefix: &str)
where
  M: VersionedMap<Comparator = dbutils::Ascend> + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  use crate::Builder;

  unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join(std::format!("{prefix}_reopen3_skipmap"));
    {
      let l = Builder::new()
        .with_create_new(true)
        .with_read(true)
        .with_write(true)
        .with_capacity(ARENA_SIZE as u32)
        .map_mut::<M, _>(&p)
        .unwrap();
      for i in 0..1000 {
        l.get_or_insert(MIN_VERSION, &key(i), &new_value(i))
          .unwrap();
      }
      l.flush().unwrap();
    }

    let l = Builder::new()
      .with_read(true)
      .with_write(true)
      .with_capacity((ARENA_SIZE * 2) as u32)
      .map_mut::<M, _>(&p)
      .unwrap();
    assert_eq!(1000, l.len());
    for i in 0..1000 {
      let k = key(i);
      let ent = l.get(MIN_VERSION, &k).unwrap();
      assert_eq!(new_value(i), ent.value());
      assert_eq!(ent.version(), 0);
      assert_eq!(ent.key(), k);
    }
  }
}

struct Person {
  id: u32,
  name: std::string::String,
}

impl Person {
  fn encoded_size(&self) -> usize {
    4 + self.name.len()
  }
}

pub(crate) fn get_or_insert_with_value<M>(l: M)
where
  M: VersionedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  let alice = Person {
    id: 1,
    name: std::string::String::from("Alice"),
  };

  let encoded_size = alice.encoded_size() as u32;

  let vb = ValueBuilder::new(encoded_size, |val| {
    assert_eq!(val.capacity(), encoded_size as usize);
    assert!(val.is_empty());
    val.put_u32_le(alice.id).unwrap();
    assert_eq!(val.len(), 4);
    assert_eq!(val.remaining(), encoded_size as usize - 4);
    assert_eq!(&*val, alice.id.to_le_bytes());
    val[..4].copy_from_slice(&alice.id.to_be_bytes());
    assert_eq!(&*val, alice.id.to_be_bytes());
    val.put_slice(alice.name.as_bytes()).unwrap();
    assert_eq!(val.len(), encoded_size as usize);
    let err = val.put_slice(&[1]).unwrap_err();
    assert_eq!(
      std::string::ToString::to_string(&err),
      "buffer does not have enough space (remaining 0, want 1)"
    );
    Ok(())
  });

  l.get_or_insert_with_value_builder::<()>(1, b"alice", vb)
    .unwrap();
}

pub(crate) fn get_or_insert_with<M>(l: M)
where
  M: VersionedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  let alice = Person {
    id: 1,
    name: std::string::String::from("Alice"),
  };

  let encoded_size = alice.encoded_size() as u32;

  let kb = KeyBuilder::new(5u8.into(), |key: &mut VacantBuffer<'_>| {
    key.put_slice(b"alice").unwrap();
    Ok(())
  });

  let vb = ValueBuilder::new(encoded_size, |val: &mut VacantBuffer<'_>| {
    assert_eq!(val.capacity(), encoded_size as usize);
    assert!(val.is_empty());
    val.put_u32_le(alice.id).unwrap();
    assert_eq!(val.len(), 4);
    assert_eq!(val.remaining(), encoded_size as usize - 4);
    assert_eq!(&*val, alice.id.to_le_bytes());
    val[..4].copy_from_slice(&alice.id.to_be_bytes());
    assert_eq!(&*val, alice.id.to_be_bytes());
    val.put_slice(alice.name.as_bytes()).unwrap();
    assert_eq!(val.len(), encoded_size as usize);
    let err = val.put_slice(&[1]).unwrap_err();
    assert_eq!(
      std::string::ToString::to_string(&err),
      "buffer does not have enough space (remaining 0, want 1)"
    );
    Ok(())
  });

  l.get_or_insert_with_builders::<(), ()>(1, kb, vb).unwrap();
}

pub(crate) fn insert<M>(l: M)
where
  M: VersionedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  let k = 0u64.to_le_bytes();
  for i in 0..100 {
    let v = new_value(i);
    let old = l.insert(MIN_VERSION, &k, &v).unwrap();
    if let Some(old) = old {
      assert_eq!(old.key(), k);
      assert_eq!(old.value(), new_value(i - 1));
    }
  }

  let ent = l.get(MIN_VERSION, &k).unwrap();
  assert_eq!(ent.key(), k);
  assert_eq!(ent.value(), new_value(99));
}

pub(crate) fn insert_with_value<M>(l: M)
where
  M: VersionedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  let alice = Person {
    id: 1,
    name: std::string::String::from("Alice"),
  };

  let encoded_size = alice.encoded_size() as u32;

  let vb = ValueBuilder::new(encoded_size, |val| {
    assert_eq!(val.capacity(), encoded_size as usize);
    assert!(val.is_empty());
    val.put_u32_le(alice.id).unwrap();
    assert_eq!(val.len(), 4);
    assert_eq!(val.remaining(), encoded_size as usize - 4);
    assert_eq!(val, alice.id.to_le_bytes());
    val[..4].copy_from_slice(&alice.id.to_be_bytes());
    assert_eq!(val, alice.id.to_be_bytes());
    val.put_slice(alice.name.as_bytes()).unwrap();
    assert_eq!(val.len(), encoded_size as usize);
    let err = val.put_slice(&[1]).unwrap_err();
    assert_eq!(
      std::string::ToString::to_string(&err),
      "buffer does not have enough space (remaining 0, want 1)"
    );
    Ok(())
  });

  l.insert_with_value_builder::<()>(1, b"alice", vb).unwrap();

  let alice2 = Person {
    id: 2,
    name: std::string::String::from("Alice"),
  };

  let vb = ValueBuilder::new(encoded_size, |val| {
    assert_eq!(val.capacity(), encoded_size as usize);
    assert!(val.is_empty());
    val.put_u32_le(alice2.id).unwrap();
    assert_eq!(val.len(), 4);
    assert_eq!(val.remaining(), encoded_size as usize - 4);
    assert_eq!(&*val, alice2.id.to_le_bytes());
    val[..4].copy_from_slice(&alice2.id.to_be_bytes());
    assert_eq!(&*val, alice2.id.to_be_bytes());
    val.put_slice(alice2.name.as_bytes()).unwrap();
    assert_eq!(val.len(), encoded_size as usize);
    let err = val.put_slice(&[1]).unwrap_err();
    assert_eq!(
      std::string::ToString::to_string(&err),
      "buffer does not have enough space (remaining 0, want 1)"
    );
    Ok(())
  });

  let old = l
    .insert_with_value_builder::<()>(1, b"alice", vb)
    .unwrap()
    .unwrap();

  assert_eq!(old.key(), b"alice");
  assert!(old.value().starts_with(&alice.id.to_be_bytes()));

  let ent = l.get(1, b"alice").unwrap();
  assert_eq!(ent.key(), b"alice");
  assert!(ent.value().starts_with(&alice2.id.to_be_bytes()));
}

pub(crate) fn insert_with<M>(l: M)
where
  M: VersionedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  let alice = Person {
    id: 1,
    name: std::string::String::from("Alice"),
  };

  let encoded_size = alice.encoded_size() as u32;

  let kb = KeyBuilder::new(5u8.into(), |key: &mut VacantBuffer<'_>| {
    key.put_slice(b"alice").unwrap();
    Ok(())
  });

  let vb = ValueBuilder::new(encoded_size, |val: &mut VacantBuffer<'_>| {
    assert_eq!(val.capacity(), encoded_size as usize);
    assert!(val.is_empty());
    val.put_u32_le(alice.id).unwrap();
    assert_eq!(val.len(), 4);
    assert_eq!(val.remaining(), encoded_size as usize - 4);
    assert_eq!(val, alice.id.to_le_bytes());
    val[..4].copy_from_slice(&alice.id.to_be_bytes());
    assert_eq!(val, alice.id.to_be_bytes());
    val.put_slice(alice.name.as_bytes()).unwrap();
    assert_eq!(val.len(), encoded_size as usize);
    let err = val.put_slice(&[1]).unwrap_err();
    assert_eq!(
      std::string::ToString::to_string(&err),
      "buffer does not have enough space (remaining 0, want 1)"
    );
    Ok(())
  });

  l.insert_with_builders::<(), ()>(1, kb, vb).unwrap();

  let alice2 = Person {
    id: 2,
    name: std::string::String::from("Alice"),
  };

  let vb = ValueBuilder::new(encoded_size, |val: &mut VacantBuffer<'_>| {
    assert_eq!(val.capacity(), encoded_size as usize);
    assert!(val.is_empty());
    val.put_u32_le(alice2.id).unwrap();
    assert_eq!(val.len(), 4);
    assert_eq!(val.remaining(), encoded_size as usize - 4);
    assert_eq!(&*val, alice2.id.to_le_bytes());
    val[..4].copy_from_slice(&alice2.id.to_be_bytes());
    assert_eq!(&*val, alice2.id.to_be_bytes());
    val.put_slice(alice2.name.as_bytes()).unwrap();
    assert_eq!(val.len(), encoded_size as usize);
    let err = val.put_slice(&[1]).unwrap_err();
    assert_eq!(
      std::string::ToString::to_string(&err),
      "buffer does not have enough space (remaining 0, want 1)"
    );
    Ok(())
  });
  let old = l
    .insert_with_builders::<(), ()>(1, kb, vb)
    .unwrap()
    .unwrap();

  assert_eq!(old.key(), b"alice");
  assert!(old.value().starts_with(&alice.id.to_be_bytes()));

  let ent = l.get(1, b"alice").unwrap();
  assert_eq!(ent.key(), b"alice");
  assert!(ent.value().starts_with(&alice2.id.to_be_bytes()));
}

pub(crate) fn get_or_remove<M>(l: M)
where
  M: VersionedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  for i in 0..100 {
    let v = new_value(i);
    l.insert(MIN_VERSION, &key(i), &v).unwrap();
  }

  for i in 0..100 {
    let k = key(i);
    let old = l.get_or_remove(MIN_VERSION, &k).unwrap().unwrap();
    assert_eq!(old.key(), k);
    assert_eq!(old.value(), new_value(i));

    let old = l.get_or_remove(MIN_VERSION, &k).unwrap().unwrap();
    assert_eq!(old.key(), k);
    assert_eq!(old.value(), new_value(i));
  }

  for i in 0..100 {
    let k = key(i);
    let ent = l.get(MIN_VERSION, &k).unwrap();
    assert_eq!(ent.key(), k);
    assert_eq!(ent.value(), new_value(i));
  }
}

pub(crate) fn remove<M>(l: M)
where
  M: VersionedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  for i in 0..100 {
    let v = new_value(i);
    l.insert(MIN_VERSION, &key(i), &v).unwrap();
  }

  for i in 0..100 {
    let k = key(i);
    // no race, remove should succeed
    let old = l
      .compare_remove(MIN_VERSION, &k, Ordering::SeqCst, Ordering::Acquire)
      .unwrap();
    assert!(old.is_none());

    // key already removed
    let old = l
      .compare_remove(MIN_VERSION, &k, Ordering::SeqCst, Ordering::Acquire)
      .unwrap();
    assert!(old.is_none());
  }

  for i in 100..150 {
    let k = key(i);
    let res = l
      .compare_remove(MIN_VERSION, &k, Ordering::SeqCst, Ordering::Acquire)
      .unwrap();
    assert!(res.is_none());
  }

  for i in 0..100 {
    let k = key(i);
    let ent = l.get(MIN_VERSION, &k);
    assert!(ent.is_none());
  }

  for i in 100..150 {
    let k = key(i);
    let ent = l.get_versioned(MIN_VERSION, &k).unwrap();
    assert_eq!(ent.key(), k);
    assert_eq!(ent.value(), None);
  }
}

pub(crate) fn remove2<M>(l: M)
where
  M: VersionedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithVersion,
  <M::Allocator as Sealed>::Trailer: Default,
{
  for i in 0..100 {
    let v = new_value(i);
    l.insert(MIN_VERSION, &key(i), &v).unwrap();
  }

  for i in 0..100 {
    let k = key(i);
    // not found, remove should succeed
    let old = l
      .compare_remove(1, &k, Ordering::SeqCst, Ordering::Acquire)
      .unwrap();
    assert!(old.is_none());

    // no-race, remove should succeed
    let old = l
      .compare_remove(MIN_VERSION, &k, Ordering::SeqCst, Ordering::Acquire)
      .unwrap();
    assert!(old.is_none());
  }

  for i in 100..150 {
    let k = key(i);
    let res = l
      .compare_remove(MIN_VERSION, &k, Ordering::SeqCst, Ordering::Acquire)
      .unwrap();
    assert!(res.is_none());
  }

  for i in 0..100 {
    let k = key(i);
    let ent = l.get(MIN_VERSION, &k);
    assert!(ent.is_none());
  }

  for i in 100..150 {
    let k = key(i);
    let ent = l.get_versioned(MIN_VERSION, &k).unwrap();
    assert_eq!(ent.key(), k);
    assert_eq!(ent.value(), None);
  }
}

#[macro_export]
#[doc(hidden)]
macro_rules! __versioned_map_tests {
  ($prefix:literal: $ty:ty) => {
    __unit_tests!($crate::tests::versioned |$prefix, $ty, $crate::tests::TEST_HIGH_COMPRESSION_OPTIONS| {
      basic,
      #[cfg(not(miri))]
      basic_large,
      iter_all_versions_mvcc,
      iter_all_versions_next,
      range_next,
      iter_all_versions_prev,
      range_prev,
      iter_all_versions_seek_ge,
      iter_all_versions_seek_lt,
      range,
      iter_latest,
      range_latest,
      get_mvcc,
      get_or_insert_with_value,
      get_or_insert_with,
      insert,
      insert_with_value,
      insert_with,
      get_or_remove,
      remove,
      remove2,
      gt,
      ge,
      lt,
      le,
    });

    #[test]
    #[cfg(feature = "memmap")]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::macro_metavars_in_unsafe)]
    fn reopen() {
      $crate::tests::versioned::reopen_mmap::<$ty>($prefix);
    }

    #[test]
    #[cfg(feature = "memmap")]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::macro_metavars_in_unsafe)]
    fn reopen2() {
      $crate::tests::versioned::reopen_mmap2::<$ty>($prefix);
    }

    #[test]
    #[cfg(feature = "memmap")]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::macro_metavars_in_unsafe)]
    fn reopen3() {
      $crate::tests::versioned::reopen_mmap3::<$ty>($prefix);
    }
  };
  // Support from golang :)
  (go $prefix:literal: $ty:ty) => {
    __unit_tests!($crate::tests::versioned |$prefix, $ty, $crate::tests::TEST_OPTIONS| {
      #[cfg(feature = "std")]
      concurrent_basic,
      #[cfg(feature = "std")]
      concurrent_basic2,
      #[cfg(feature = "std")]
      concurrent_one_key,
      #[cfg(feature = "std")]
      concurrent_one_key2,
    });

    // #[cfg(not(miri))]
    mod high_compression {
      use super::*;

      __unit_tests!($crate::tests::versioned |$prefix, $ty, $crate::tests::TEST_HIGH_COMPRESSION_OPTIONS| {
        #[cfg(feature = "std")]
        concurrent_basic,
        #[cfg(feature = "std")]
        concurrent_basic2,
        #[cfg(feature = "std")]
        concurrent_one_key,
        #[cfg(feature = "std")]
        concurrent_one_key2,
      });
    }

    __unit_tests!($crate::tests::versioned |$prefix, $ty, $crate::tests::BIG_TEST_OPTIONS| {
      #[cfg(all(feature = "std", not(miri)))]
      concurrent_basic_big_values,
    });
  }
}
