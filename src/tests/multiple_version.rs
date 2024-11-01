#![allow(dead_code)]

use core::sync::atomic::Ordering;

use dbutils::buffer::VacantBuffer;

use crate::{allocator::WithVersion, multiple_version::Map, KeyBuilder, ValueBuilder, MIN_VERSION};

use super::*;

pub(crate) fn empty<M>(l: M)
where
  M: Map<[u8], [u8]>,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  let mut it = l.iter(MIN_VERSION);

  assert!(it.seek_lower_bound::<[u8]>(Bound::Unbounded).is_none());
  assert!(it.seek_upper_bound::<[u8]>(Bound::Unbounded).is_none());
  assert!(it.seek_lower_bound(Bound::Included(b"aaa")).is_none());
  assert!(it.seek_upper_bound(Bound::Excluded(b"aaa")).is_none());
  assert!(it.seek_lower_bound(Bound::Excluded(b"aaa")).is_none());
  assert!(it.seek_upper_bound(Bound::Included(b"aaa")).is_none());
  assert!(l.first(MIN_VERSION,).is_none());
  assert!(l.last(MIN_VERSION,).is_none());

  assert!(l.get(MIN_VERSION, b"aaa".as_slice()).is_none());
  assert!(!l.contains_key(MIN_VERSION, b"aaa".as_slice()));
  assert!(l.allocated() > 0);
  assert!(l.capacity() > 0);
  assert_eq!(l.remaining(), l.capacity() - l.allocated());
}

pub(crate) fn full<M>(l: M)
where
  M: Map<[u8], [u8]>,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  let mut found_arena_full = false;

  for i in 0..100 {
    if let Err(e) = l.get_or_insert(
      MIN_VERSION,
      make_int_key(i).as_slice(),
      make_value(i).as_slice(),
    ) {
      assert!(matches!(
        e.unwrap_right(),
        Error::Arena(ArenaError::InsufficientSpace { .. })
      ));
      found_arena_full = true;
      break;
    }
  }

  assert!(found_arena_full);
}

pub(crate) fn basic<M>(mut l: M)
where
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  // Try adding values.
  l.get_or_insert(0, b"key1".as_slice(), make_value(1).as_slice())
    .unwrap();
  l.get_or_insert(0, b"key3".as_slice(), make_value(3).as_slice())
    .unwrap();
  l.get_or_insert(0, b"key2".as_slice(), make_value(2).as_slice())
    .unwrap();

  {
    let mut it = l.iter_all_versions(0);
    let ent = it.seek_lower_bound(Bound::Included(b"key1")).unwrap();
    assert_eq!(ent.key(), b"key1".as_slice());
    assert_eq!(ent.raw_key(), b"key1".as_slice());
    assert_eq!(ent.value().unwrap(), make_value(1).as_slice());
    assert_eq!(ent.raw_value().unwrap(), make_value(1).as_slice());
    assert_eq!(ent.version(), 0);

    let ent = it
      .seek_lower_bound(Bound::Included(b"key2".as_slice()))
      .unwrap();
    assert_eq!(ent.key(), b"key2".as_slice());
    assert_eq!(ent.raw_key(), b"key2".as_slice());
    assert_eq!(ent.value().unwrap(), make_value(2).as_slice());
    assert_eq!(ent.raw_value().unwrap(), make_value(2).as_slice());
    assert_eq!(ent.version(), 0);

    let ent = it
      .seek_lower_bound(Bound::Included(b"key3".as_slice()))
      .unwrap();
    assert_eq!(ent.key(), b"key3".as_slice());
    assert_eq!(ent.raw_key(), b"key3".as_slice());
    assert_eq!(ent.value().unwrap(), make_value(3).as_slice());
    assert_eq!(ent.raw_value().unwrap(), make_value(3).as_slice());
    assert_eq!(ent.version(), 0);
  }

  l.get_or_insert(1, "a".as_bytes(), [].as_slice()).unwrap();
  l.get_or_insert(2, "a".as_bytes(), [].as_slice()).unwrap();

  {
    let mut it = l.iter_all_versions(2);
    let ent = it
      .seek_lower_bound(Bound::Included(b"a".as_slice()))
      .unwrap();
    assert_eq!(ent.key(), b"a".as_slice());
    assert_eq!(ent.raw_key(), b"a".as_slice());
    assert_eq!(ent.value().unwrap(), &[]);
    assert_eq!(ent.raw_value().unwrap(), &[]);
    assert_eq!(ent.version(), 2);

    let ent = it.next().unwrap();
    assert_eq!(ent.key(), b"a".as_slice());
    assert_eq!(ent.raw_key(), b"a".as_slice());
    assert_eq!(ent.value().unwrap(), &[]);
    assert_eq!(ent.raw_value().unwrap(), &[]);
    assert_eq!(ent.version(), 1);
  }

  l.get_or_insert(2, "b".as_bytes(), [].as_slice()).unwrap();
  l.get_or_insert(1, "b".as_bytes(), [].as_slice()).unwrap();

  {
    let mut it = l.iter_all_versions(2);
    let ent = it.seek_lower_bound(Bound::Included(b"b")).unwrap();
    assert_eq!(ent.key(), b"b");
    assert_eq!(ent.raw_key(), b"b");
    assert_eq!(ent.value().unwrap(), &[]);
    assert_eq!(ent.raw_value().unwrap(), &[]);
    assert_eq!(ent.version(), 2);

    let ent = it.next().unwrap();
    assert_eq!(ent.key(), b"b");
    assert_eq!(ent.raw_key(), b"b");
    assert_eq!(ent.value().unwrap(), &[]);
    assert_eq!(ent.raw_value().unwrap(), &[]);
    assert_eq!(ent.version(), 1);

    let ent = it.head().unwrap();
    assert_eq!(ent.key(), b"b");
    assert_eq!(ent.raw_key(), b"b");
    assert_eq!(ent.value().unwrap(), &[]);
    assert_eq!(ent.raw_value().unwrap(), &[]);
    assert_eq!(ent.version(), 1);
  }

  l.get_or_insert(2, b"b".as_slice(), [].as_slice())
    .unwrap()
    .unwrap();

  assert!(l
    .get_or_insert(2, b"c".as_slice(), [].as_slice())
    .unwrap()
    .is_none());

  unsafe {
    l.clear().unwrap();
  }

  let l = l.clone();
  {
    let mut it = l.iter_all_versions(0);
    assert!(it.seek_lower_bound::<[u8]>(Bound::Unbounded).is_none());
    assert!(it.seek_upper_bound::<[u8]>(Bound::Unbounded).is_none());
  }
  assert!(l.is_empty());

  #[cfg(feature = "memmap")]
  l.flush().unwrap();

  #[cfg(feature = "memmap")]
  l.flush_async().unwrap();
}

pub(crate) fn iter_all_versions_mvcc<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  l.get_or_insert(1, b"a".as_slice(), b"a1".as_slice())
    .unwrap();
  l.get_or_insert(3, b"a".as_slice(), b"a2".as_slice())
    .unwrap();
  l.get_or_insert(1, b"c".as_slice(), b"c1".as_slice())
    .unwrap();
  l.get_or_insert(3, b"c".as_slice(), b"c2".as_slice())
    .unwrap();

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
  assert!(it.seek_lower_bound::<[u8]>(Bound::Unbounded).is_none());
  assert!(it.seek_upper_bound::<[u8]>(Bound::Unbounded).is_none());

  let mut it = l.iter_all_versions(1);
  let ent = it.seek_lower_bound::<[u8]>(Bound::Unbounded).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value().unwrap(), b"a1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = it.seek_upper_bound::<[u8]>(Bound::Unbounded).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value().unwrap(), b"c1".as_slice());
  assert_eq!(ent.version(), 1);

  let mut it = l.iter_all_versions(2);
  let ent = it.seek_lower_bound::<[u8]>(Bound::Unbounded).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value().unwrap(), b"a1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = it.seek_upper_bound::<[u8]>(Bound::Unbounded).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value().unwrap(), b"c1".as_slice());
  assert_eq!(ent.version(), 1);

  let mut it = l.iter_all_versions(3);

  let ent = it.seek_upper_bound(Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value().unwrap(), b"a1".as_slice(),);
  assert_eq!(ent.version(), 1);

  let ent = ent.prev().unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value().unwrap(), b"a2".as_slice());
  assert_eq!(ent.version(), 3);

  let ent = it
    .seek_upper_bound(Bound::Included(b"c".as_slice()))
    .unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value().unwrap(), b"c1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = ent.prev().unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value().unwrap(), b"c2".as_slice());
  assert_eq!(ent.version(), 3);

  let ent = it.seek_lower_bound(Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value().unwrap(), b"c2".as_slice());
  assert_eq!(ent.version(), 3);

  let ent = it
    .seek_lower_bound(Bound::Included(b"c".as_slice()))
    .unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value().unwrap(), b"c2".as_slice());
  assert_eq!(ent.version(), 3);
}

pub(crate) fn get_mvcc<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  l.get_or_insert(1, b"a".as_slice(), b"a1".as_slice())
    .unwrap();
  l.get_or_insert(3, b"a".as_slice(), b"a2".as_slice())
    .unwrap();
  l.get_or_insert(1, b"c".as_slice(), b"c1".as_slice())
    .unwrap();
  l.get_or_insert(3, b"c".as_slice(), b"c2".as_slice())
    .unwrap();

  let ent = l.get(1, b"a".as_slice()).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value(), b"a1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.get(2, b"a".as_slice()).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value(), b"a1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.get(3, b"a".as_slice()).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value(), b"a2".as_slice());
  assert_eq!(ent.version(), 3);

  let ent = l.get(4, b"a".as_slice()).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value(), b"a2".as_slice());
  assert_eq!(ent.version(), 3);

  assert!(l.get(0, b"b").is_none());
  assert!(l.get(1, b"b").is_none());
  assert!(l.get(2, b"b").is_none());
  assert!(l.get(3, b"b").is_none());
  assert!(l.get(4, b"b").is_none());

  let ent = l.get(1, b"c".as_slice()).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.get(2, b"c".as_slice()).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.get(3, b"c".as_slice()).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c2".as_slice());
  assert_eq!(ent.version(), 3);

  let ent = l.get(4, b"c".as_slice()).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c2".as_slice());
  assert_eq!(ent.version(), 3);

  assert!(l.get(5, b"d").is_none());
}

pub(crate) fn gt<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  l.get_or_insert(1, b"a".as_slice(), b"a1".as_slice())
    .unwrap();
  l.get_or_insert(3, b"a".as_slice(), b"a2".as_slice())
    .unwrap();
  l.get_or_insert(1, b"c".as_slice(), b"c1".as_slice())
    .unwrap();
  l.get_or_insert(3, b"c".as_slice(), b"c2".as_slice())
    .unwrap();
  l.get_or_insert(5, b"c".as_slice(), b"c3".as_slice())
    .unwrap();

  assert!(l.lower_bound(0, Bound::Excluded(b"a".as_slice())).is_none());
  assert!(l.lower_bound(0, Bound::Excluded(b"b")).is_none());
  assert!(l.lower_bound(0, Bound::Excluded(b"c".as_slice())).is_none());

  let ent = l.lower_bound(1, Bound::Excluded(b"")).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value(), b"a1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(2, Bound::Excluded(b"")).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value(), b"a1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(3, Bound::Excluded(b"")).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value(), b"a2".as_slice());
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(1, Bound::Excluded(b"a".as_slice())).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(2, Bound::Excluded(b"a".as_slice())).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(3, Bound::Excluded(b"a".as_slice())).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c2".as_slice());
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(1, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(2, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(3, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c2".as_slice());
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(4, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c2".as_slice());
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(5, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c3".as_slice());
  assert_eq!(ent.version(), 5);

  let ent = l.lower_bound(6, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c3".as_slice());
  assert_eq!(ent.version(), 5);

  assert!(l.lower_bound(1, Bound::Excluded(b"c".as_slice())).is_none());
  assert!(l.lower_bound(2, Bound::Excluded(b"c".as_slice())).is_none());
  assert!(l.lower_bound(3, Bound::Excluded(b"c".as_slice())).is_none());
  assert!(l.lower_bound(4, Bound::Excluded(b"c".as_slice())).is_none());
  assert!(l.lower_bound(5, Bound::Excluded(b"c".as_slice())).is_none());
  assert!(l.lower_bound(6, Bound::Excluded(b"c".as_slice())).is_none());
}

pub(crate) fn ge<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  l.get_or_insert(1, b"a".as_slice(), b"a1".as_slice())
    .unwrap();
  l.get_or_insert(3, b"a".as_slice(), b"a2".as_slice())
    .unwrap();
  l.get_or_insert(1, b"c".as_slice(), b"c1".as_slice())
    .unwrap();
  l.get_or_insert(3, b"c".as_slice(), b"c2".as_slice())
    .unwrap();

  assert!(l
    .lower_bound(MIN_VERSION, Bound::Included(b"a".as_slice()))
    .is_none());
  assert!(l.lower_bound(MIN_VERSION, Bound::Included(b"b")).is_none());
  assert!(l
    .lower_bound(MIN_VERSION, Bound::Included(b"c".as_slice()))
    .is_none());

  let ent = l.lower_bound(1, Bound::Included(b"a".as_slice())).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value(), b"a1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(2, Bound::Included(b"a".as_slice())).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value(), b"a1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(3, Bound::Included(b"a".as_slice())).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value(), b"a2".as_slice());
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(4, Bound::Included(b"a".as_slice())).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value(), b"a2".as_slice());
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(1, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(2, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(3, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c2".as_slice());
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(4, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c2".as_slice());
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(1, Bound::Included(b"c".as_slice())).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(2, Bound::Included(b"c".as_slice())).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(3, Bound::Included(b"c".as_slice())).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c2".as_slice());
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(4, Bound::Included(b"c".as_slice())).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c2".as_slice());
  assert_eq!(ent.version(), 3);

  assert!(l.lower_bound(MIN_VERSION, Bound::Included(b"d")).is_none());
  assert!(l.lower_bound(1, Bound::Included(b"d")).is_none());
  assert!(l.lower_bound(2, Bound::Included(b"d")).is_none());
  assert!(l.lower_bound(3, Bound::Included(b"d")).is_none());
  assert!(l.lower_bound(4, Bound::Included(b"d")).is_none());
}

pub(crate) fn le<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  l.get_or_insert(1, b"a".as_slice(), b"a1".as_slice())
    .unwrap();
  l.get_or_insert(3, b"a".as_slice(), b"a2".as_slice())
    .unwrap();
  l.get_or_insert(1, b"c".as_slice(), b"c1".as_slice())
    .unwrap();
  l.get_or_insert(3, b"c".as_slice(), b"c2".as_slice())
    .unwrap();

  assert!(l
    .upper_bound(MIN_VERSION, Bound::Included(b"a".as_slice()))
    .is_none());
  assert!(l.upper_bound(MIN_VERSION, Bound::Included(b"b")).is_none());
  assert!(l
    .upper_bound(MIN_VERSION, Bound::Included(b"c".as_slice()))
    .is_none());

  let ent = l.upper_bound(1, Bound::Included(b"a".as_slice())).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value(), b"a1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(2, Bound::Included(b"a".as_slice())).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value(), b"a1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(3, Bound::Included(b"a".as_slice())).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value(), b"a2".as_slice());
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(4, Bound::Included(b"a".as_slice())).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value(), b"a2".as_slice());
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(1, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value(), b"a1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(2, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value(), b"a1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(3, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value(), b"a2".as_slice());
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(4, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value(), b"a2".as_slice());
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(1, Bound::Included(b"c".as_slice())).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(2, Bound::Included(b"c".as_slice())).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(3, Bound::Included(b"c".as_slice())).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c2".as_slice());
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(4, Bound::Included(b"c".as_slice())).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c2".as_slice());
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(1, Bound::Included(b"d")).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(2, Bound::Included(b"d")).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(3, Bound::Included(b"d")).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c2".as_slice());
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(4, Bound::Included(b"d")).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c2".as_slice());
  assert_eq!(ent.version(), 3);
}

pub(crate) fn lt<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  l.get_or_insert(1, b"a".as_slice(), b"a1".as_slice())
    .unwrap();
  l.get_or_insert(3, b"a".as_slice(), b"a2".as_slice())
    .unwrap();
  l.get_or_insert(1, b"c".as_slice(), b"c1".as_slice())
    .unwrap();
  l.get_or_insert(3, b"c".as_slice(), b"c2".as_slice())
    .unwrap();

  assert!(l
    .upper_bound(MIN_VERSION, Bound::Excluded(b"a".as_slice()))
    .is_none());
  assert!(l.upper_bound(MIN_VERSION, Bound::Excluded(b"b")).is_none());
  assert!(l
    .upper_bound(MIN_VERSION, Bound::Excluded(b"c".as_slice()))
    .is_none());
  assert!(l.upper_bound(1, Bound::Excluded(b"a".as_slice())).is_none());
  assert!(l.upper_bound(2, Bound::Excluded(b"a".as_slice())).is_none());

  let ent = l.upper_bound(1, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value(), b"a1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(2, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value(), b"a1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(3, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value(), b"a2".as_slice());
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(4, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value(), b"a2".as_slice());
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(1, Bound::Excluded(b"c".as_slice())).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value(), b"a1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(2, Bound::Excluded(b"c".as_slice())).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value(), b"a1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(3, Bound::Excluded(b"c".as_slice())).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value(), b"a2".as_slice());
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(4, Bound::Excluded(b"c".as_slice())).unwrap();
  assert_eq!(ent.key(), b"a".as_slice());
  assert_eq!(ent.value(), b"a2".as_slice());
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(1, Bound::Excluded(b"d")).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(2, Bound::Excluded(b"d")).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c1".as_slice());
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(3, Bound::Excluded(b"d")).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c2".as_slice());
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(4, Bound::Excluded(b"d")).unwrap();
  assert_eq!(ent.key(), b"c".as_slice());
  assert_eq!(ent.value(), b"c2".as_slice());
  assert_eq!(ent.version(), 3);
}

#[cfg(not(miri))]
pub(crate) fn basic_large<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  let n = 1000;

  for i in 0..n {
    l.get_or_insert(MIN_VERSION, key(i).as_slice(), new_value(i).as_slice())
      .unwrap();
  }

  for i in 0..n {
    let k = key(i);
    let ent = l.get(MIN_VERSION, k.as_slice()).unwrap();
    assert_eq!(new_value(i).as_slice(), ent.value());
    assert_eq!(ent.version(), 0);
    assert_eq!(ent.key(), k.as_slice());
  }

  assert_eq!(n, l.len());
}

#[cfg(all(
  feature = "std",
  any(
    all(test, not(miri)),
    all_tests,
    test_sync_versioned_concurrent,
    test_sync_versioned_concurrent_with_optimistic_freelist,
    test_sync_versioned_concurrent_with_pessimistic_freelist
  )
))]
pub(crate) fn concurrent_basic<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone + Send + 'static,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  #[cfg(not(miri))]
  const N: usize = 1000;
  #[cfg(miri)]
  const N: usize = 200;

  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      l.get_or_insert(MIN_VERSION, key(i).as_slice(), new_value(i).as_slice())
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
        l.get(MIN_VERSION, k.as_slice()).unwrap().value(),
        new_value(i).as_slice(),
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
  any(
    all(test, not(miri)),
    all_tests,
    test_sync_versioned_concurrent,
    test_sync_versioned_concurrent_with_optimistic_freelist,
    test_sync_versioned_concurrent_with_pessimistic_freelist
  )
))]
pub(crate) fn concurrent_basic2<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone + Send + 'static,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  #[cfg(not(miri))]
  const N: usize = 1000;
  #[cfg(miri)]
  const N: usize = 200;

  for i in (0..N).rev() {
    let l1 = l.clone();
    let l2 = l.clone();
    std::thread::Builder::new()
      .name(format!("fullmap-concurrent-basic2-writer-{i}-1"))
      .spawn(move || {
        let _ = l1.insert(MIN_VERSION, int_key(i).as_slice(), new_value(i).as_slice());
      })
      .unwrap();

    std::thread::Builder::new()
      .name(format!("fullmap-concurrent-basic2-writer{i}-2"))
      .spawn(move || {
        let _ = l2.insert(MIN_VERSION, int_key(i).as_slice(), new_value(i).as_slice());
      })
      .unwrap();
  }
  while l.refs() > 1 {
    ::core::hint::spin_loop();
  }
  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      let k = int_key(i);
      assert_eq!(
        l.get(MIN_VERSION, k.as_slice()).unwrap().value(),
        new_value(i).as_slice(),
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
  any(
    all(test, not(miri)),
    all_tests,
    test_sync_versioned_concurrent,
    test_sync_versioned_concurrent_with_optimistic_freelist,
    test_sync_versioned_concurrent_with_pessimistic_freelist
  )
))]
pub(crate) fn concurrent_basic_big_values<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone + Send + 'static,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  #[cfg(not(any(miri, feature = "loom")))]
  const N: usize = 100;
  #[cfg(any(miri, feature = "loom"))]
  const N: usize = 20;

  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      l.get_or_insert(MIN_VERSION, key(i).as_slice(), big_value(i).as_slice())
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
        l.get(MIN_VERSION, k.as_slice()).unwrap().value(),
        big_value(i).as_slice(),
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
  any(
    all(test, not(miri)),
    all_tests,
    test_sync_versioned_concurrent,
    test_sync_versioned_concurrent_with_optimistic_freelist,
    test_sync_versioned_concurrent_with_pessimistic_freelist
  )
))]
pub(crate) fn concurrent_one_key<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone + Send + 'static,
  <M::Allocator as Sealed>::Node: WithVersion,
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
      let _ = l.get_or_insert(MIN_VERSION, b"thekey".as_slice(), make_value(i).as_slice());
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
      let ent = l.get(MIN_VERSION, b"thekey".as_slice()).unwrap();
      let val = ent.value();
      let num: usize = core::str::from_utf8(&val[1..]).unwrap().parse().unwrap();
      assert!((0..N).contains(&num));

      let mut it = l.iter_all_versions(MIN_VERSION);
      let ent = it
        .seek_lower_bound(Bound::Included(b"thekey".as_slice()))
        .unwrap();
      let val = ent.value().unwrap();
      let num: usize = core::str::from_utf8(&val[1..]).unwrap().parse().unwrap();
      assert!((0..N).contains(&num));
      assert_eq!(ent.key(), b"thekey".as_slice());
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
  any(
    all(test, not(miri)),
    all_tests,
    test_sync_versioned_concurrent,
    test_sync_versioned_concurrent_with_optimistic_freelist,
    test_sync_versioned_concurrent_with_pessimistic_freelist
  )
))]
pub(crate) fn concurrent_one_key2<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone + Send + 'static,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  use core::sync::atomic::Ordering;
  use std::sync::Arc;

  #[cfg(not(miri))]
  const N: usize = 100;
  #[cfg(miri)]
  const N: usize = 20;

  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      let _ = l.insert(MIN_VERSION, b"thekey".as_slice(), make_value(i).as_slice());
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
      let ent = l.get(MIN_VERSION, b"thekey".as_slice()).unwrap();
      let val = ent.value();
      let num: usize = core::str::from_utf8(&val[1..]).unwrap().parse().unwrap();
      assert!((0..N).contains(&num));

      let mut it = l.iter_all_versions(MIN_VERSION);
      let ent = it
        .seek_lower_bound(Bound::Included(b"thekey".as_slice()))
        .unwrap();
      let val = ent.value().unwrap();
      let num: usize = core::str::from_utf8(&val[1..]).unwrap().parse().unwrap();
      assert!((0..N).contains(&num));
      assert_eq!(ent.key(), b"thekey".as_slice());
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
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  const N: usize = 100;

  for i in (0..N).rev() {
    l.get_or_insert(
      MIN_VERSION,
      make_int_key(i).as_slice(),
      make_value(i).as_slice(),
    )
    .unwrap();
  }

  let mut it = l.iter_all_versions(MIN_VERSION);
  let mut ent = it.seek_lower_bound::<[u8]>(Bound::Unbounded).unwrap();
  for i in 0..N {
    assert_eq!(ent.key(), make_int_key(i).as_slice());
    assert_eq!(ent.value().unwrap(), make_value(i).as_slice());
    if i != N - 1 {
      ent = it.next().unwrap();
    }
  }

  assert!(it.next().is_none());
}

pub(crate) fn iter_all_versions_next_by_entry<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  const N: usize = 100;

  for i in (0..N).rev() {
    l.get_or_insert(
      MIN_VERSION,
      make_int_key(i).as_slice(),
      make_value(i).as_slice(),
    )
    .unwrap();
  }

  let mut ent = l.first(MIN_VERSION);

  let mut i = 0;
  while let Some(ref entry) = ent {
    assert_eq!(entry.key(), make_int_key(i).as_slice());
    assert_eq!(entry.value(), make_value(i).as_slice());
    ent = entry.next();
    i += 1;
  }
  assert_eq!(i, N);
}

pub(crate) fn iter_all_versions_next_by_versioned_entry<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  const N: usize = 100;

  for i in 0..N {
    let k = make_int_key(i);
    let v = make_value(i);
    l.insert(MIN_VERSION, k.as_slice(), v.as_slice()).unwrap();

    l.get_or_remove(MIN_VERSION + 1, k.as_slice()).unwrap();
  }

  let mut ent = l.first(MIN_VERSION);
  let mut i = 0;
  while let Some(ref entry) = ent {
    assert_eq!(entry.key(), make_int_key(i).as_slice());
    assert_eq!(entry.value(), make_value(i).as_slice());
    ent = entry.next();
    i += 1;
  }
  assert_eq!(i, N);

  let mut ent = l.first_versioned(MIN_VERSION + 1);
  let mut i = 0;
  while let Some(ref entry) = ent {
    if i % 2 == 1 {
      assert_eq!(entry.version(), MIN_VERSION);
      assert_eq!(entry.key(), make_int_key(i / 2).as_slice());
      assert_eq!(entry.value().unwrap(), make_value(i / 2).as_slice());
    } else {
      assert_eq!(entry.version(), MIN_VERSION + 1);
      assert_eq!(entry.key(), make_int_key(i / 2).as_slice());
      assert!(entry.value().is_none());
    }

    ent = entry.next();
    i += 1;
  }
  assert_eq!(i, 2 * N);
  let ent = l.first(MIN_VERSION + 1);
  assert!(ent.is_none(), "{:?}", ent);
}

pub(crate) fn range_next<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  const N: usize = 100;

  for i in (0..N).rev() {
    l.get_or_insert(
      MIN_VERSION,
      make_int_key(i).as_slice(),
      make_value(i).as_slice(),
    )
    .unwrap();
  }

  let upper = make_int_key(50);
  let mut i = 0;
  let mut it = l.range(MIN_VERSION, ..=upper.as_slice());
  for ent in &mut it {
    assert_eq!(ent.key(), make_int_key(i).as_slice());
    assert_eq!(ent.value(), make_value(i).as_slice());
    i += 1;
  }

  assert_eq!(i, 51);
}

pub(crate) fn iter_all_versions_prev<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(
      MIN_VERSION,
      make_int_key(i).as_slice(),
      make_value(i).as_slice(),
    )
    .unwrap();
  }

  let mut it = l.iter_all_versions(MIN_VERSION);
  let mut ent = it.seek_upper_bound::<[u8]>(Bound::Unbounded).unwrap();
  for i in (0..N).rev() {
    assert_eq!(ent.key(), make_int_key(i).as_slice());
    assert_eq!(ent.value().unwrap(), make_value(i).as_slice());
    if i != 0 {
      ent = it.next_back().unwrap();
    }
  }

  assert!(it.next_back().is_none());
}

pub(crate) fn iter_all_versions_prev_by_entry<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(
      MIN_VERSION,
      make_int_key(i).as_slice(),
      make_value(i).as_slice(),
    )
    .unwrap();
  }

  let mut ent = l.last(MIN_VERSION);

  let mut i = 0;
  while let Some(ref entry) = ent {
    i += 1;
    assert_eq!(entry.key(), make_int_key(N - i).as_slice());
    assert_eq!(entry.value(), make_value(N - i).as_slice());
    ent = entry.prev();
  }
  assert_eq!(i, N);
}

pub(crate) fn iter_all_versions_prev_by_versioned_entry<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  const N: usize = 100;

  for i in (0..N).rev() {
    let k = make_int_key(i);
    let v = make_value(i);
    l.insert(MIN_VERSION, k.as_slice(), v.as_slice()).unwrap();

    l.get_or_remove(MIN_VERSION + 1, k.as_slice()).unwrap();
  }

  let mut ent = l.last(MIN_VERSION);
  let mut i = 0;
  while let Some(ref entry) = ent {
    i += 1;
    assert_eq!(entry.key(), make_int_key(N - i).as_slice());
    assert_eq!(entry.value(), make_value(N - i).as_slice());
    ent = entry.prev();
  }
  assert_eq!(i, N);

  let mut ent = l.last_versioned(MIN_VERSION + 1);
  let mut i = 0;
  while let Some(ref entry) = ent {
    if i % 2 == 0 {
      assert_eq!(entry.version(), MIN_VERSION);
      assert_eq!(entry.key(), make_int_key(N - 1 - i / 2).as_slice(),);
      assert_eq!(entry.value().unwrap(), make_value(N - 1 - i / 2).as_slice());
      i += 1;
    } else {
      assert_eq!(entry.version(), MIN_VERSION + 1);
      assert_eq!(entry.key(), make_int_key(N - 1 - i / 2).as_slice());
      assert!(entry.value().is_none());
      i += 1;
    }
    ent = entry.prev();
  }
  assert_eq!(i, 2 * N);
  let ent = l.last(MIN_VERSION + 1);
  assert!(ent.is_none(), "{:?}", ent);
}

pub(crate) fn range_prev<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(
      MIN_VERSION,
      make_int_key(i).as_slice(),
      make_value(i).as_slice(),
    )
    .unwrap();
  }

  let lower = make_int_key(50);
  let it = l.range(MIN_VERSION, lower.as_slice()..);
  let mut i = 99;
  for ent in it.rev() {
    assert_eq!(ent.key(), make_int_key(i).as_slice());
    assert_eq!(ent.value(), make_value(i).as_slice());
    i -= 1;
  }
}

pub(crate) fn iter_all_versions_seek_ge<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  const N: usize = 100;

  for i in (0..N).rev() {
    let v = i * 10 + 1000;
    l.get_or_insert(
      MIN_VERSION,
      make_int_key(v).as_slice(),
      make_value(v).as_slice(),
    )
    .unwrap();
  }

  let mut it = l.iter_all_versions(MIN_VERSION);
  let ent = it.seek_lower_bound(Bound::Included(b"")).unwrap();
  assert_eq!(ent.key(), make_int_key(1000).as_slice());
  assert_eq!(ent.value().unwrap(), make_value(1000).as_slice());

  let ent = it.seek_lower_bound(Bound::Included(b"01000")).unwrap();
  assert_eq!(ent.key(), make_int_key(1000).as_slice());
  assert_eq!(ent.value().unwrap(), make_value(1000).as_slice());

  let ent = it.seek_lower_bound(Bound::Included(b"01005")).unwrap();
  assert_eq!(ent.key(), make_int_key(1010).as_slice());
  assert_eq!(ent.value().unwrap(), make_value(1010).as_slice());

  let ent = it.seek_lower_bound(Bound::Included(b"01010")).unwrap();
  assert_eq!(ent.key(), make_int_key(1010).as_slice());
  assert_eq!(ent.value().unwrap(), make_value(1010).as_slice());

  let ent = it.seek_lower_bound(Bound::Included(b"01020")).unwrap();
  assert_eq!(ent.key(), make_int_key(1020).as_slice());
  assert_eq!(ent.value().unwrap(), make_value(1020).as_slice());

  let ent = it.seek_lower_bound(Bound::Included(b"01200")).unwrap();
  assert_eq!(ent.key(), make_int_key(1200).as_slice());
  assert_eq!(ent.value().unwrap(), make_value(1200).as_slice());

  let ent = it.seek_lower_bound(Bound::Included(b"01100")).unwrap();
  assert_eq!(ent.key(), make_int_key(1100).as_slice());
  assert_eq!(ent.value().unwrap(), make_value(1100).as_slice());

  let ent = it.seek_lower_bound(Bound::Included(b"99999"));
  assert!(ent.is_none());

  l.get_or_insert(MIN_VERSION, [].as_slice(), [].as_slice())
    .unwrap();
  let ent = it.seek_lower_bound(Bound::Included(b"")).unwrap();
  assert_eq!(ent.key(), &[]);
  assert_eq!(ent.value().unwrap(), &[]);

  let ent = it.seek_lower_bound(Bound::Included(b"")).unwrap();
  assert_eq!(ent.key(), &[]);
  assert_eq!(ent.value().unwrap(), &[]);
}

pub(crate) fn iter_all_versions_seek_lt<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  const N: usize = 100;

  for i in (0..N).rev() {
    let v = i * 10 + 1000;
    l.get_or_insert(
      MIN_VERSION,
      make_int_key(v).as_slice(),
      make_value(v).as_slice(),
    )
    .unwrap();
  }

  let mut it = l.iter_all_versions(MIN_VERSION);
  assert!(it.seek_upper_bound(Bound::Excluded(b"")).is_none());

  let ent = it.seek_upper_bound(Bound::Excluded(b"01000"));
  assert!(ent.is_none());

  let ent = it.seek_upper_bound(Bound::Excluded(b"01001")).unwrap();
  assert_eq!(ent.key(), make_int_key(1000).as_slice());
  assert_eq!(ent.value().unwrap(), make_value(1000).as_slice());

  let ent = it.seek_upper_bound(Bound::Excluded(b"01991")).unwrap();
  assert_eq!(ent.key(), make_int_key(1990).as_slice());
  assert_eq!(ent.value().unwrap(), make_value(1990).as_slice());

  let ent = it.seek_upper_bound(Bound::Excluded(b"99999")).unwrap();
  assert_eq!(ent.key(), make_int_key(1990).as_slice());
  assert_eq!(ent.value().unwrap(), make_value(1990).as_slice());

  l.get_or_insert(MIN_VERSION, [].as_slice(), [].as_slice())
    .unwrap();
  assert!(l
    .as_ref()
    .upper_bound::<[u8]>(MIN_VERSION, Bound::Excluded(&[]))
    .is_none());

  let ent = it.seek_upper_bound(Bound::Excluded(b""));
  assert!(ent.is_none());

  let ent = it.seek_upper_bound(Bound::Excluded(b"\x01")).unwrap();
  assert_eq!(ent.key(), &[]);
  assert_eq!(ent.value().unwrap(), &[]);
}

pub(crate) fn range<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  for i in 1..10 {
    l.get_or_insert(
      MIN_VERSION,
      make_int_key(i).as_slice(),
      make_value(i).as_slice(),
    )
    .unwrap();
  }

  let k3 = make_int_key(3);
  let k7 = make_int_key(7);
  let mut it = l.range(MIN_VERSION, k3.as_slice()..k7.as_slice()).clone();
  assert_eq!(it.start_bound(), Bound::Included(&k3.as_slice()));
  assert_eq!(it.end_bound(), Bound::Excluded(&k7.as_slice()));

  for i in 3..=6 {
    let k = make_int_key(i);
    let ent = it.seek_lower_bound(Bound::Included(k.as_slice())).unwrap();
    assert_eq!(ent.key(), make_int_key(i).as_slice());
    assert_eq!(ent.value(), make_value(i).as_slice());
  }

  for i in 1..3 {
    let k = make_int_key(i);
    let ent = it.seek_lower_bound(Bound::Included(k.as_slice())).unwrap();
    assert_eq!(ent.key(), make_int_key(3).as_slice(),);
    assert_eq!(ent.value(), make_value(3).as_slice());
  }

  for i in 7..10 {
    let k = make_int_key(i);
    assert!(it.seek_lower_bound(Bound::Included(k.as_slice())).is_none());
  }

  for i in 7..10 {
    let k = make_int_key(i);
    let ent = it.seek_upper_bound(Bound::Included(k.as_slice())).unwrap();
    assert_eq!(ent.key(), make_int_key(6).as_slice());
    assert_eq!(ent.value(), make_value(6).as_slice());
  }

  let ent = it
    .seek_lower_bound(Bound::Included(make_int_key(6).as_slice()))
    .unwrap();
  assert_eq!(ent.key(), make_int_key(6).as_slice());
  assert_eq!(ent.value(), make_value(6).as_slice());

  assert!(it.next().is_none());

  let ent = it
    .seek_upper_bound(Bound::Included(make_int_key(6).as_slice()))
    .unwrap();
  assert_eq!(ent.key(), make_int_key(6).as_slice());
  assert_eq!(ent.value(), make_value(6).as_slice());

  assert!(it.next().is_none());

  for i in 4..=7 {
    let k = make_int_key(i);
    let ent = it.seek_upper_bound(Bound::Excluded(k.as_slice())).unwrap();
    assert_eq!(ent.key(), make_int_key(i - 1).as_slice());
    assert_eq!(ent.value(), make_value(i - 1).as_slice());
  }

  for i in 7..10 {
    let k = make_int_key(i);
    let ent = it.seek_upper_bound(Bound::Excluded(k.as_slice())).unwrap();
    assert_eq!(ent.key(), make_int_key(6).as_slice());
    assert_eq!(ent.value(), make_value(6).as_slice());
  }

  for i in 1..3 {
    let k = make_int_key(i);
    let ent = it.seek_lower_bound(Bound::Excluded(k.as_slice())).unwrap();
    assert_eq!(ent.key(), make_int_key(3).as_slice());
    assert_eq!(ent.value(), make_value(3).as_slice());
  }

  for i in 1..4 {
    let k = make_int_key(i);
    assert!(it.seek_upper_bound(Bound::Excluded(k.as_slice())).is_none());
  }

  let ent = it
    .seek_upper_bound(Bound::Excluded(make_int_key(4).as_slice()))
    .unwrap();
  assert_eq!(ent.key(), make_int_key(3).as_slice());
  assert_eq!(ent.value(), make_value(3).as_slice());

  let ent = it.next_back().unwrap();
  assert_eq!(ent.key(), make_int_key(6).as_slice());
  assert_eq!(ent.value(), make_value(6).as_slice());
}

pub(crate) fn iter_latest<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(
      MIN_VERSION,
      make_int_key(i).as_slice(),
      make_value(i).as_slice(),
    )
    .unwrap();
  }

  for i in 50..N {
    l.get_or_insert(
      1,
      make_int_key(i).as_slice(),
      make_value(i + 1000).as_slice(),
    )
    .unwrap();
  }

  for i in 0..50 {
    l.get_or_insert(
      2,
      make_int_key(i).as_slice(),
      make_value(i + 1000).as_slice(),
    )
    .unwrap();
  }

  let mut it = l.iter(4);

  let mut num = 0;
  for i in 0..N {
    let ent = it.next().unwrap();

    assert_eq!(
      ent.key(),
      make_int_key(i).as_slice(),
      "{} != {}",
      core::str::from_utf8(ent.key()).unwrap(),
      core::str::from_utf8(make_int_key(i).as_slice()).unwrap()
    );
    assert_eq!(
      ent.value(),
      make_value(i + 1000).as_slice(),
      "{} != {}",
      core::str::from_utf8(ent.value()).unwrap(),
      core::str::from_utf8(make_value(i + 1000).as_slice()).unwrap()
    );

    num += 1;
  }
  assert_eq!(num, N);
}

pub(crate) fn range_latest<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(
      MIN_VERSION,
      make_int_key(i).as_slice(),
      make_value(i).as_slice(),
    )
    .unwrap();
  }

  for i in 50..N {
    l.get_or_insert(
      1,
      make_int_key(i).as_slice(),
      make_value(i + 1000).as_slice(),
    )
    .unwrap();
  }

  for i in 0..50 {
    l.get_or_insert(
      2,
      make_int_key(i).as_slice(),
      make_value(i + 1000).as_slice(),
    )
    .unwrap();
  }

  let mut it = l.range::<[u8], _>(4, ..);
  let mut num = 0;
  for i in 0..N {
    let ent = it.next().unwrap();
    assert_eq!(ent.key(), make_int_key(i).as_slice());
    assert_eq!(ent.value(), make_value(i + 1000).as_slice());

    num += 1;
  }
  assert_eq!(num, N);
}

#[cfg(feature = "memmap")]
pub(crate) fn reopen_mmap<M>(prefix: &str)
where
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  use crate::Options;

  unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join(std::format!("{prefix}_reopen_skipmap"));
    {
      let l = Options::new()
        .with_create_new(true)
        .with_read(true)
        .with_write(true)
        .with_capacity(ARENA_SIZE as u32)
        .map_mut::<[u8], [u8], M, _>(&p)
        .unwrap();
      for i in 0..1000 {
        l.get_or_insert(MIN_VERSION, key(i).as_slice(), new_value(i).as_slice())
          .unwrap();
      }
      l.flush().unwrap();
    }

    let l = Options::new()
      .with_read(true)
      .with_write(true)
      .with_capacity(ARENA_SIZE as u32)
      .map::<[u8], [u8], M, _>(&p)
      .unwrap();
    assert_eq!(1000, l.len());
    for i in 0..1000 {
      let k = key(i);
      let ent = l.get(MIN_VERSION, k.as_slice()).unwrap();
      assert_eq!(new_value(i).as_slice(), ent.value());
      assert_eq!(ent.version(), 0);
      assert_eq!(ent.key(), k.as_slice());
    }
  }
}

#[cfg(feature = "memmap")]
pub(crate) fn reopen_mmap2<M>(prefix: &str)
where
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  use crate::Options;

  unsafe {
    use rand::seq::SliceRandom;

    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join(::std::format!("{prefix}_reopen2_skipmap"));
    {
      let l = Options::new()
        .with_create_new(true)
        .with_read(true)
        .with_write(true)
        .with_capacity(ARENA_SIZE as u32)
        .map_mut::<[u8], [u8], M, _>(&p)
        .unwrap();
      let mut data = (0..1000).collect::<::std::vec::Vec<usize>>();
      data.shuffle(&mut rand::thread_rng());
      for i in &data {
        let i = *i;
        l.get_or_insert(i as u64, key(i).as_slice(), new_value(i).as_slice())
          .unwrap();
      }
      l.flush_async().unwrap();
      assert_eq!(l.maximum_version(), 999);
      assert_eq!(l.minimum_version(), 0);

      for i in data {
        let k = key(i);
        let ent = l.get(i as u64, k.as_slice()).unwrap();
        assert_eq!(new_value(i).as_slice(), ent.value());
        assert_eq!(ent.version(), i as u64);
        assert_eq!(ent.key(), k.as_slice());
      }
    }

    let l = Options::new()
      .with_read(true)
      .with_write(true)
      .with_capacity(ARENA_SIZE as u32)
      .map::<[u8], [u8], M, _>(&p)
      .unwrap();
    assert_eq!(1000, l.len());
    let mut data = (0..1000).collect::<::std::vec::Vec<usize>>();
    data.shuffle(&mut rand::thread_rng());
    for i in data {
      let k = key(i);
      let ent = l.get(i as u64, k.as_slice()).unwrap();
      assert_eq!(new_value(i).as_slice(), ent.value());
      assert_eq!(ent.version(), i as u64);
      assert_eq!(ent.key(), k.as_slice());
    }
    assert_eq!(l.maximum_version(), 999);
    assert_eq!(l.minimum_version(), 0);
  }
}

#[cfg(feature = "memmap")]
pub(crate) fn reopen_mmap3<M>(prefix: &str)
where
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  use crate::Options;

  unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join(std::format!("{prefix}_reopen3_skipmap"));
    {
      let l = Options::new()
        .with_create_new(true)
        .with_read(true)
        .with_write(true)
        .with_capacity(ARENA_SIZE as u32)
        .map_mut::<[u8], [u8], M, _>(&p)
        .unwrap();
      for i in 0..1000 {
        l.get_or_insert(MIN_VERSION, key(i).as_slice(), new_value(i).as_slice())
          .unwrap();
      }
      l.flush().unwrap();
    }

    let l = Options::new()
      .with_read(true)
      .with_write(true)
      .with_capacity((ARENA_SIZE * 2) as u32)
      .map_mut::<[u8], [u8], M, _>(&p)
      .unwrap();
    assert_eq!(1000, l.len());
    for i in 0..1000 {
      let k = key(i);
      let ent = l.get(MIN_VERSION, k.as_slice()).unwrap();
      assert_eq!(new_value(i).as_slice(), ent.value());
      assert_eq!(ent.version(), 0);
      assert_eq!(ent.key(), k.as_slice());
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
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  let alice = Person {
    id: 1,
    name: std::string::String::from("Alice"),
  };

  let encoded_size = alice.encoded_size();

  let vb = ValueBuilder::new(encoded_size, |val: &mut VacantBuffer<'_>| {
    assert_eq!(val.capacity(), encoded_size);
    assert!(val.is_empty());
    val.put_u32_le(alice.id).unwrap();
    assert_eq!(val.len(), 4);
    assert_eq!(val.remaining(), encoded_size - 4);
    assert_eq!(&*val, alice.id.to_le_bytes());
    val[..4].copy_from_slice(&alice.id.to_be_bytes());
    assert_eq!(&*val, alice.id.to_be_bytes());
    val.put_slice(alice.name.as_bytes()).unwrap();
    assert_eq!(val.len(), encoded_size);
    let err = val.put_slice(&[1]).unwrap_err();
    assert_eq!(
      std::string::ToString::to_string(&err),
      "incomplete buffer data: expected 0 bytes for decoding, but only 1 bytes were available"
    );
    Ok(())
  });

  l.get_or_insert_with_value_builder::<()>(1, b"alice".as_slice(), vb)
    .unwrap();
}

pub(crate) fn get_or_insert_with<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  let alice = Person {
    id: 1,
    name: std::string::String::from("Alice"),
  };

  let encoded_size = alice.encoded_size();

  let kb = KeyBuilder::new(5u8.into(), |key: &mut VacantBuffer<'_>| {
    key.put_slice(b"alice").unwrap();
    Ok(())
  });

  let vb = ValueBuilder::new(encoded_size, |val: &mut VacantBuffer<'_>| {
    assert_eq!(val.capacity(), encoded_size);
    assert!(val.is_empty());
    val.put_u32_le(alice.id).unwrap();
    assert_eq!(val.len(), 4);
    assert_eq!(val.remaining(), encoded_size - 4);
    assert_eq!(&*val, alice.id.to_le_bytes());
    val[..4].copy_from_slice(&alice.id.to_be_bytes());
    assert_eq!(&*val, alice.id.to_be_bytes());
    val.put_slice(alice.name.as_bytes()).unwrap();
    assert_eq!(val.len(), encoded_size);
    let err = val.put_slice(&[1]).unwrap_err();
    assert_eq!(
      std::string::ToString::to_string(&err),
      "incomplete buffer data: expected 0 bytes for decoding, but only 1 bytes were available"
    );
    Ok(())
  });

  l.get_or_insert_with_builders::<(), ()>(1, kb, vb).unwrap();
}

pub(crate) fn insert<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  let k = 0u64.to_le_bytes();
  for i in 0..100 {
    let v = new_value(i);
    let old = l.insert(MIN_VERSION, k.as_slice(), v.as_slice()).unwrap();
    if let Some(old) = old {
      assert_eq!(old.key(), k.as_slice());
      assert_eq!(old.value(), new_value(i - 1).as_slice());
    }
  }

  let ent = l.get(MIN_VERSION, k.as_slice()).unwrap();
  assert_eq!(ent.key(), k.as_slice());
  assert_eq!(ent.value(), new_value(99).as_slice());
}

pub(crate) fn insert_with_value<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  let alice = Person {
    id: 1,
    name: std::string::String::from("Alice"),
  };

  let encoded_size = alice.encoded_size();

  let vb = ValueBuilder::new(encoded_size, |val: &mut VacantBuffer<'_>| {
    assert_eq!(val.capacity(), encoded_size);
    assert!(val.is_empty());
    val.put_u32_le(alice.id).unwrap();
    assert_eq!(val.len(), 4);
    assert_eq!(val.remaining(), encoded_size - 4);
    assert_eq!(val, alice.id.to_le_bytes());
    val[..4].copy_from_slice(&alice.id.to_be_bytes());
    assert_eq!(val, alice.id.to_be_bytes());
    val.put_slice(alice.name.as_bytes()).unwrap();
    assert_eq!(val.len(), encoded_size);
    let err = val.put_slice(&[1]).unwrap_err();
    assert_eq!(
      std::string::ToString::to_string(&err),
      "incomplete buffer data: expected 0 bytes for decoding, but only 1 bytes were available"
    );
    Ok(())
  });

  l.insert_with_value_builder::<()>(1, b"alice".as_slice(), vb)
    .unwrap();

  let alice2 = Person {
    id: 2,
    name: std::string::String::from("Alice"),
  };

  let vb = ValueBuilder::new(encoded_size, |val: &mut VacantBuffer<'_>| {
    assert_eq!(val.capacity(), encoded_size);
    assert!(val.is_empty());
    val.put_u32_le(alice2.id).unwrap();
    assert_eq!(val.len(), 4);
    assert_eq!(val.remaining(), encoded_size - 4);
    assert_eq!(&*val, alice2.id.to_le_bytes());
    val[..4].copy_from_slice(&alice2.id.to_be_bytes());
    assert_eq!(&*val, alice2.id.to_be_bytes());
    val.put_slice(alice2.name.as_bytes()).unwrap();
    assert_eq!(val.len(), encoded_size);
    let err = val.put_slice(&[1]).unwrap_err();
    assert_eq!(
      std::string::ToString::to_string(&err),
      "incomplete buffer data: expected 0 bytes for decoding, but only 1 bytes were available"
    );
    Ok(())
  });

  let old = l
    .insert_with_value_builder::<()>(1, b"alice".as_slice(), vb)
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
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  let alice = Person {
    id: 1,
    name: std::string::String::from("Alice"),
  };

  let encoded_size = alice.encoded_size();

  let kb = KeyBuilder::new(5u8.into(), |key: &mut VacantBuffer<'_>| {
    key.put_slice(b"alice").unwrap();
    Ok(())
  });

  let vb = ValueBuilder::new(encoded_size, |val: &mut VacantBuffer<'_>| {
    assert_eq!(val.capacity(), encoded_size);
    assert!(val.is_empty());
    val.put_u32_le(alice.id).unwrap();
    assert_eq!(val.len(), 4);
    assert_eq!(val.remaining(), encoded_size - 4);
    assert_eq!(val, alice.id.to_le_bytes());
    val[..4].copy_from_slice(&alice.id.to_be_bytes());
    assert_eq!(val, alice.id.to_be_bytes());
    val.put_slice(alice.name.as_bytes()).unwrap();
    assert_eq!(val.len(), encoded_size);
    let err = val.put_slice(&[1]).unwrap_err();
    assert_eq!(
      std::string::ToString::to_string(&err),
      "incomplete buffer data: expected 0 bytes for decoding, but only 1 bytes were available"
    );
    Ok(())
  });

  l.insert_with_builders::<(), ()>(1, kb, vb).unwrap();

  let alice2 = Person {
    id: 2,
    name: std::string::String::from("Alice"),
  };

  let vb = ValueBuilder::new(encoded_size, |val: &mut VacantBuffer<'_>| {
    assert_eq!(val.capacity(), encoded_size);
    assert!(val.is_empty());
    val.put_u32_le(alice2.id).unwrap();
    assert_eq!(val.len(), 4);
    assert_eq!(val.remaining(), encoded_size - 4);
    assert_eq!(&*val, alice2.id.to_le_bytes());
    val[..4].copy_from_slice(&alice2.id.to_be_bytes());
    assert_eq!(&*val, alice2.id.to_be_bytes());
    val.put_slice(alice2.name.as_bytes()).unwrap();
    assert_eq!(val.len(), encoded_size);
    let err = val.put_slice(&[1]).unwrap_err();
    assert_eq!(
      std::string::ToString::to_string(&err),
      "incomplete buffer data: expected 0 bytes for decoding, but only 1 bytes were available"
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
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  for i in 0..100 {
    let v = new_value(i);
    l.insert(MIN_VERSION, key(i).as_slice(), v.as_slice())
      .unwrap();
  }

  for i in 0..100 {
    let k = key(i);
    let old = l.get_or_remove(MIN_VERSION, k.as_slice()).unwrap().unwrap();
    assert_eq!(old.key(), k.as_slice());
    assert_eq!(old.value(), new_value(i).as_slice());

    let old = l.get_or_remove(MIN_VERSION, k.as_slice()).unwrap().unwrap();
    assert_eq!(old.key(), k.as_slice());
    assert_eq!(old.value(), new_value(i).as_slice());
  }

  for i in 0..100 {
    let k = key(i);
    let ent = l.get(MIN_VERSION, k.as_slice()).unwrap();
    assert_eq!(ent.key(), k.as_slice());
    assert_eq!(ent.value(), new_value(i).as_slice());
  }
}

pub(crate) fn remove<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  for i in 0..100 {
    let v = new_value(i);
    l.insert(MIN_VERSION, key(i).as_slice(), v.as_slice())
      .unwrap();
  }

  for i in 0..100 {
    let k = key(i);
    // no race, remove should succeed
    let old = l
      .compare_remove(
        MIN_VERSION,
        k.as_slice(),
        Ordering::SeqCst,
        Ordering::Acquire,
      )
      .unwrap();
    assert!(old.is_none());

    // key already removed
    let old = l
      .compare_remove(
        MIN_VERSION,
        k.as_slice(),
        Ordering::SeqCst,
        Ordering::Acquire,
      )
      .unwrap();
    assert!(old.is_none());
  }

  for i in 100..150 {
    let k = key(i);
    let res = l
      .compare_remove(
        MIN_VERSION,
        k.as_slice(),
        Ordering::SeqCst,
        Ordering::Acquire,
      )
      .unwrap();
    assert!(res.is_none());
  }

  for i in 0..100 {
    let k = key(i);
    let ent = l.get(MIN_VERSION, k.as_slice());
    assert!(ent.is_none());
  }

  for i in 100..150 {
    let k = key(i);
    let ent = l.get_versioned(MIN_VERSION, k.as_slice()).unwrap();
    assert_eq!(ent.key(), k.as_slice());
    assert_eq!(ent.value(), None);
  }
}

pub(crate) fn remove2<M>(l: M)
where
  M: Map<[u8], [u8]> + Clone,
  <M::Allocator as Sealed>::Node: WithVersion,
{
  for i in 0..100 {
    let v = new_value(i);
    l.insert(MIN_VERSION, key(i).as_slice(), v.as_slice())
      .unwrap();
  }

  for i in 0..100 {
    let k = key(i);
    // not found, remove should succeed
    let old = l
      .compare_remove(1, k.as_slice(), Ordering::SeqCst, Ordering::Acquire)
      .unwrap();
    assert!(old.is_none());

    // no-race, remove should succeed
    let old = l
      .compare_remove(
        MIN_VERSION,
        k.as_slice(),
        Ordering::SeqCst,
        Ordering::Acquire,
      )
      .unwrap();
    assert!(old.is_none());
  }

  for i in 100..150 {
    let k = key(i);
    let res = l
      .compare_remove(
        MIN_VERSION,
        k.as_slice(),
        Ordering::SeqCst,
        Ordering::Acquire,
      )
      .unwrap();
    assert!(res.is_none());
  }

  for i in 0..100 {
    let k = key(i);
    let ent = l.get(MIN_VERSION, k.as_slice());
    assert!(ent.is_none());
  }

  for i in 100..150 {
    let k = key(i);
    let ent = l.get_versioned(MIN_VERSION, k.as_slice()).unwrap();
    assert_eq!(ent.key(), k.as_slice());
    assert_eq!(ent.value(), None);
  }
}

#[macro_export]
#[doc(hidden)]
macro_rules! __versioned_map_tests {
  ($prefix:literal: $ty:ty) => {
    __unit_tests!($crate::tests::multiple_version |$prefix, $ty, $crate::tests::TEST_OPTIONS| {
      empty,
      basic,
      #[cfg(not(miri))]
      basic_large,
      iter_all_versions_mvcc,
      iter_all_versions_next,
      iter_all_versions_next_by_entry,
      iter_all_versions_next_by_versioned_entry,
      range_next,
      iter_all_versions_prev,
      iter_all_versions_prev_by_entry,
      iter_all_versions_prev_by_versioned_entry,
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

    __unit_tests!($crate::tests::multiple_version |$prefix, $ty, $crate::tests::TEST_FULL_OPTIONS| {
      full,
    });

    #[test]
    #[cfg(feature = "memmap")]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::macro_metavars_in_unsafe)]
    fn reopen() {
      $crate::tests::multiple_version::reopen_mmap::<$ty>($prefix);
    }

    #[test]
    #[cfg(feature = "memmap")]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::macro_metavars_in_unsafe)]
    fn reopen2() {
      $crate::tests::multiple_version::reopen_mmap2::<$ty>($prefix);
    }

    #[test]
    #[cfg(feature = "memmap")]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::macro_metavars_in_unsafe)]
    fn reopen3() {
      $crate::tests::multiple_version::reopen_mmap3::<$ty>($prefix);
    }
  };
  // Support from golang :)
  (go $prefix:literal: $ty:ty => $opts:path) => {
    __unit_tests!($crate::tests::multiple_version |$prefix, $ty, $opts| {
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
    // mod high_compression {
    //   use super::*;

    //   __unit_tests!($crate::tests::multiple_version |$prefix, $ty, $crate::tests::TEST_HIGH_COMPRESSION_OPTIONS| {
    //     #[cfg(feature = "std")]
    //     concurrent_basic,
    //     #[cfg(feature = "std")]
    //     concurrent_basic2,
    //     #[cfg(feature = "std")]
    //     concurrent_one_key,
    //     #[cfg(feature = "std")]
    //     concurrent_one_key2,
    //   });
    // }

    __unit_tests!($crate::tests::multiple_version |$prefix, $ty, $crate::tests::BIG_TEST_OPTIONS| {
      #[cfg(all(feature = "std", not(miri)))]
      concurrent_basic_big_values,
    });
  }
}
