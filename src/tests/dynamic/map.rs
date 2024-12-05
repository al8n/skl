#![allow(dead_code)]

use core::ops::Bound;

use crate::{
  allocator::Sealed,
  error::{ArenaError, Error},
};

use core::sync::atomic::Ordering;

use dbutils::buffer::VacantBuffer;

use crate::{
  allocator::WithoutVersion,
  dynamic::{unique::Map, Ascend},
  KeyBuilder, ValueBuilder,
};

use super::*;

pub(crate) fn empty<M>(l: M)
where
  M: Map,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  let mut it = l.iter();

  assert!(it.seek_lower_bound::<[u8]>(Bound::Unbounded).is_none());
  assert!(it.seek_upper_bound::<[u8]>(Bound::Unbounded).is_none());
  assert!(it
    .seek_lower_bound::<[u8]>(Bound::Included(b"aaa"))
    .is_none());
  assert!(it
    .seek_upper_bound::<[u8]>(Bound::Excluded(b"aaa"))
    .is_none());
  assert!(it
    .seek_lower_bound::<[u8]>(Bound::Excluded(b"aaa"))
    .is_none());
  assert!(it
    .seek_upper_bound::<[u8]>(Bound::Included(b"aaa"))
    .is_none());
  assert!(l.first().is_none());
  assert!(l.last().is_none());

  assert!(l.get(b"aaa".as_slice()).is_none());
  assert!(!l.contains_key(b"aaa".as_slice()));
  assert!(l.allocated() > 0);
  assert!(l.capacity() > 0);
  assert_eq!(l.remaining(), l.capacity() - l.allocated());
}

pub(crate) fn full<M>(l: M)
where
  M: Map,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  let mut found_arena_full = false;

  for i in 0..100 {
    if let Err(e) = l.get_or_insert(make_int_key(i).as_slice(), make_value(i).as_slice()) {
      assert!(matches!(
        e,
        Error::Arena(ArenaError::InsufficientSpace { .. })
      ));
      found_arena_full = true;
      break;
    }
  }

  assert!(found_arena_full);
}

pub(crate) fn basic<M>(l: M)
where
  M: Map + Clone,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  // Try adding values.
  l.get_or_insert(b"key1".as_slice(), make_value(1).as_slice())
    .unwrap();
  l.get_or_insert(b"key3".as_slice(), make_value(3).as_slice())
    .unwrap();
  l.get_or_insert(b"key2".as_slice(), make_value(2).as_slice())
    .unwrap();

  {
    let mut it = l.iter();
    let ent = it.seek_lower_bound(Bound::Included(b"key1")).unwrap();
    assert_eq!(ent.key(), b"key1");
    assert_eq!(ent.value(), make_value(1).as_slice());

    let ent = it.seek_lower_bound(Bound::Included(b"key2")).unwrap();
    assert_eq!(ent.key(), b"key2");
    assert_eq!(ent.value(), make_value(2).as_slice());

    let ent = it.seek_lower_bound(Bound::Included(b"key3")).unwrap();
    assert_eq!(ent.key(), b"key3");
    assert_eq!(ent.value(), make_value(3).as_slice());
  }

  l.get_or_insert("a".as_bytes(), [].as_slice()).unwrap();
  l.get_or_insert("a".as_bytes(), [].as_slice()).unwrap();

  {
    let mut it = l.iter();
    let ent = it.seek_lower_bound(Bound::Included(b"a")).unwrap();
    assert_eq!(ent.key(), b"a");
    assert_eq!(ent.value(), &[]);

    let ent = it.next().unwrap();
    assert_eq!(ent.key(), b"key1");
    assert_eq!(ent.value(), make_value(1).as_slice());
  }

  l.get_or_insert("b".as_bytes(), [].as_slice()).unwrap();
  l.get_or_insert("b".as_bytes(), [].as_slice()).unwrap();

  {
    let mut it = l.iter();
    let ent = it.seek_lower_bound(Bound::Included(b"b")).unwrap();
    assert_eq!(ent.key(), b"b");
    assert_eq!(ent.value(), &[]);

    let ent = it.next().unwrap();
    assert_eq!(ent.key(), b"key1");
    assert_eq!(ent.value(), make_value(1).as_slice());

    let ent = it.head().unwrap();
    assert_eq!(ent.key(), b"key1");
    assert_eq!(ent.value(), make_value(1).as_slice());
  }

  l.get_or_insert(b"b".as_slice(), [].as_slice())
    .unwrap()
    .unwrap();

  assert!(l
    .get_or_insert(b"c".as_slice(), [].as_slice())
    .unwrap()
    .is_none());

  #[cfg(feature = "memmap")]
  l.flush().unwrap();

  #[cfg(feature = "memmap")]
  l.flush_async().unwrap();
}

pub(crate) fn get<M>(l: M)
where
  M: Map + Clone,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  l.get_or_insert(b"a".as_slice(), b"a1".as_slice()).unwrap();
  l.get_or_insert(b"a".as_slice(), b"a2".as_slice()).unwrap();
  l.get_or_insert(b"c".as_slice(), b"c1".as_slice()).unwrap();
  l.get_or_insert(b"c".as_slice(), b"c2".as_slice()).unwrap();

  let ent = l.get(b"a").unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");

  let ent = l.get(b"a").unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");

  let ent = l.get(b"a").unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");

  l.insert(b"a".as_slice(), b"a2".as_slice()).unwrap();

  let ent = l.get(b"a").unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");

  assert!(l.get(b"b").is_none());
  assert!(l.get(b"b").is_none());
  assert!(l.get(b"b").is_none());
  assert!(l.get(b"b").is_none());
  assert!(l.get(b"b").is_none());

  let ent = l.get(b"c").unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");

  let ent = l.get(b"c").unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");

  assert!(l.get(b"d").is_none());
}

pub(crate) fn gt<M>(l: M)
where
  M: Map + Clone,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  l.get_or_insert(b"a".as_slice(), b"a1".as_slice()).unwrap();
  l.get_or_insert(b"a".as_slice(), b"a2".as_slice()).unwrap();
  l.get_or_insert(b"c".as_slice(), b"c1".as_slice()).unwrap();
  l.get_or_insert(b"c".as_slice(), b"c2".as_slice()).unwrap();
  l.get_or_insert(b"c".as_slice(), b"c3".as_slice()).unwrap();

  assert!(l.lower_bound(Bound::Excluded(b"a")).is_some());
  assert!(l.lower_bound(Bound::Excluded(b"b".as_slice())).is_some());
  assert!(l.lower_bound(Bound::Excluded(b"c")).is_none());

  let ent = l.lower_bound(Bound::Excluded(b"")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");

  let ent = l.lower_bound(Bound::Excluded(b"")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");

  let ent = l.lower_bound(Bound::Excluded(b"a")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");

  let ent = l.lower_bound(Bound::Excluded(b"b".as_slice())).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");

  let ent = l.lower_bound(Bound::Excluded(b"b".as_slice())).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");

  assert!(l.lower_bound(Bound::Excluded(b"c")).is_none());
}

pub(crate) fn ge<M>(l: M)
where
  M: Map + Clone,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  l.get_or_insert(b"a".as_slice(), b"a1".as_slice()).unwrap();
  l.get_or_insert(b"a".as_slice(), b"a2".as_slice()).unwrap();
  l.get_or_insert(b"c".as_slice(), b"c1".as_slice()).unwrap();
  l.get_or_insert(b"c".as_slice(), b"c2".as_slice()).unwrap();

  assert!(l.lower_bound(Bound::Included(b"a")).is_some());
  assert!(l.lower_bound(Bound::Included(b"b")).is_some());
  assert!(l.lower_bound(Bound::Included(b"c")).is_some());

  let ent = l.lower_bound(Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");

  let ent = l.lower_bound(Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");

  l.insert(b"a".as_slice(), b"a2".as_slice()).unwrap();

  let ent = l.lower_bound(Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");

  let ent = l.lower_bound(Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");

  let ent = l.lower_bound(Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");

  let ent = l.lower_bound(Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");

  let ent = l.lower_bound(Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");

  assert!(l.lower_bound(Bound::Included(b"d")).is_none());
}

pub(crate) fn le<M>(l: M)
where
  M: Map + Clone,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  l.get_or_insert(b"a".as_slice(), b"a1".as_slice()).unwrap();
  l.get_or_insert(b"a".as_slice(), b"a2".as_slice()).unwrap();
  l.get_or_insert(b"c".as_slice(), b"c1".as_slice()).unwrap();
  l.get_or_insert(b"c".as_slice(), b"c2".as_slice()).unwrap();

  assert!(l.upper_bound(Bound::Included(b"a")).is_some());
  assert!(l.upper_bound(Bound::Included(b"b")).is_some());
  assert!(l.upper_bound(Bound::Included(b"c")).is_some());

  let ent = l.upper_bound(Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");

  let ent = l.upper_bound(Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");

  let ent = l.upper_bound(Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");

  let ent = l.upper_bound(Bound::Included(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
}

pub(crate) fn lt<M>(l: M)
where
  M: Map + Clone,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  l.get_or_insert(b"a".as_slice(), b"a1".as_slice()).unwrap();
  l.get_or_insert(b"a".as_slice(), b"a2".as_slice()).unwrap();
  l.get_or_insert(b"c".as_slice(), b"c1".as_slice()).unwrap();
  l.get_or_insert(b"c".as_slice(), b"c2".as_slice()).unwrap();

  assert!(l.upper_bound(Bound::Excluded(b"a")).is_none());
  assert!(l.upper_bound(Bound::Excluded(b"b".as_slice())).is_some());
  assert!(l.upper_bound(Bound::Excluded(b"c")).is_some());

  let ent = l.upper_bound(Bound::Excluded(b"b".as_slice())).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");

  let ent = l.upper_bound(Bound::Excluded(b"c")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");

  let ent = l.upper_bound(Bound::Excluded(b"d".as_slice())).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
}

#[cfg(not(miri))]
pub(crate) fn basic_large<M>(l: M)
where
  M: Map + Clone,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  let n = 1000;

  for i in 0..n {
    l.get_or_insert(key(i).as_slice(), new_value(i).as_slice())
      .unwrap();
  }

  for i in 0..n {
    let k = key(i);
    let ent = l.get(k.as_slice()).unwrap();
    assert_eq!(new_value(i).as_slice(), ent.value());

    assert_eq!(ent.key(), k.as_slice());
  }

  assert_eq!(n, l.len());
}

#[cfg(all(
  feature = "std",
  any(
    all(test, not(miri)),
    all_skl_tests,
    test_dynamic_sync_map_concurrent,
    test_dynamic_sync_map_concurrent_with_optimistic_freelist,
    test_dynamic_sync_map_concurrent_with_pessimistic_freelist,
  )
))]
pub(crate) fn concurrent_basic_two_maps<M>(l: M)
where
  M: Map + Clone + Send + 'static,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  #[cfg(not(miri))]
  const N: usize = 1000;
  #[cfg(miri)]
  const N: usize = 100;

  let l2 = M::create_from_allocator(l.allocator().clone(), Ascend::new()).unwrap();

  for i in (0..N / 2).rev() {
    let l = l.clone();
    let l2 = l2.clone();
    std::thread::spawn(move || {
      l.get_or_insert(key(i).as_slice(), new_value(i).as_slice())
        .unwrap();
    });
    std::thread::spawn(move || {
      l2.get_or_insert(key(i + N / 2).as_slice(), new_value(i + N / 2).as_slice())
        .unwrap();
    });
  }
  while l.refs() > 2 {
    ::core::hint::spin_loop();
  }
  for i in 0..N / 2 {
    let l = l.clone();
    let l2 = l2.clone();
    std::thread::spawn(move || {
      let k = key(i);
      assert_eq!(
        l.get(k.as_slice()).unwrap().value(),
        new_value(i).as_slice(),
        "broken: {i}"
      );
    });
    std::thread::spawn(move || {
      let k = key(i + N / 2);
      assert_eq!(
        l2.get(k.as_slice()).unwrap().value(),
        new_value(i + N / 2).as_slice(),
        "broken: {i}"
      );
    });
  }
  while l.refs() > 2 {
    ::core::hint::spin_loop();
  }
}

#[cfg(all(
  feature = "std",
  any(
    all(test, not(miri)),
    all_skl_tests,
    test_dynamic_sync_map_concurrent,
    test_dynamic_sync_map_concurrent_with_optimistic_freelist,
    test_dynamic_sync_map_concurrent_with_pessimistic_freelist,
  )
))]
pub(crate) fn concurrent_basic<M>(l: M)
where
  M: Map + Clone + Send + 'static,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  #[cfg(not(miri))]
  const N: usize = 1000;
  #[cfg(miri)]
  const N: usize = 100;

  for i in (0..N).rev() {
    let l = l.clone();
    std::thread::spawn(move || {
      l.get_or_insert(key(i).as_slice(), new_value(i).as_slice())
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
        l.get(k.as_slice()).unwrap().value(),
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
    all_skl_tests,
    test_dynamic_sync_map_concurrent,
    test_dynamic_sync_map_concurrent_with_optimistic_freelist,
    test_dynamic_sync_map_concurrent_with_pessimistic_freelist
  )
))]
pub(crate) fn concurrent_basic2<M>(l: M)
where
  M: Map + Clone + Send + 'static,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  #[cfg(not(miri))]
  const N: usize = 1000;
  #[cfg(miri)]
  const N: usize = 100;

  for i in 0..N {
    let l1 = l.clone();
    let l2 = l.clone();
    std::thread::Builder::new()
      .name(std::format!("map-concurrent-basic2-writer-{i}-1"))
      .spawn(move || {
        let _ = l1.insert(int_key(i).as_slice(), new_value(i).as_slice());
      })
      .unwrap();

    std::thread::Builder::new()
      .name(std::format!("map-concurrent-basic2-writer{i}-2"))
      .spawn(move || {
        let _ = l2.insert(int_key(i).as_slice(), new_value(i).as_slice());
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
        l.get(k.as_slice()).unwrap().value(),
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
    all_skl_tests,
    test_dynamic_sync_map_concurrent,
    test_dynamic_sync_map_concurrent_with_optimistic_freelist,
    test_dynamic_sync_map_concurrent_with_pessimistic_freelist
  )
))]
pub(crate) fn concurrent_basic_big_values<M>(l: M)
where
  M: Map + Clone + Send + 'static,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  #[cfg(not(miri))]
  const N: usize = 1000;
  #[cfg(miri)]
  const N: usize = 100;

  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      l.get_or_insert(key(i).as_slice(), big_value(i).as_slice())
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
        l.get(k.as_slice()).unwrap().value(),
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
    all_skl_tests,
    test_dynamic_sync_map_concurrent,
    test_dynamic_sync_map_concurrent_with_optimistic_freelist,
    test_dynamic_sync_map_concurrent_with_pessimistic_freelist
  )
))]
pub(crate) fn concurrent_one_key<M>(l: M)
where
  M: Map + Clone + Send + 'static,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  use std::sync::Arc;

  #[cfg(not(miri))]
  const N: usize = 1000;
  #[cfg(miri)]
  const N: usize = 100;

  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      let _ = l.get_or_insert(b"thekey".as_slice(), make_value(i).as_slice());
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
      let ent = l.get(b"thekey").unwrap();
      let val = ent.value();
      let num: usize = core::str::from_utf8(&val[1..]).unwrap().parse().unwrap();
      assert!((0..N).contains(&num));

      let mut it = l.iter();
      let ent = it.seek_lower_bound(Bound::Included(b"thekey")).unwrap();
      let val = ent.value();
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
  any(
    all(test, not(miri)),
    all_skl_tests,
    test_dynamic_sync_map_concurrent,
    test_dynamic_sync_map_concurrent_with_optimistic_freelist,
    test_dynamic_sync_map_concurrent_with_pessimistic_freelist
  )
))]
pub(crate) fn concurrent_one_key2<M>(l: M)
where
  M: Map + Clone + Send + 'static,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  use std::sync::Arc;

  #[cfg(not(miri))]
  const N: usize = 100;
  #[cfg(miri)]
  const N: usize = 20;

  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      let _ = l.insert(b"thekey".as_slice(), make_value(i).as_slice());
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
      let ent = l.get::<[u8]>(b"thekey").unwrap();
      let val = ent.value();
      let num: usize = core::str::from_utf8(&val[1..]).unwrap().parse().unwrap();
      assert!((0..N).contains(&num));

      let mut it = l.iter();
      let ent = it
        .seek_lower_bound(Bound::Included(b"thekey".as_slice()))
        .unwrap();
      let val = ent.value();
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

pub(crate) fn iter_with_tombstone_next<M>(l: M)
where
  M: Map + Clone,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  const N: usize = 100;

  for i in (0..N).rev() {
    l.get_or_insert(make_int_key(i).as_slice(), make_value(i).as_slice())
      .unwrap();
  }

  let mut it = l.iter();
  let mut ent = it.seek_lower_bound::<[u8]>(Bound::Unbounded).unwrap();
  for i in 0..N {
    assert_eq!(ent.key(), make_int_key(i).as_slice());
    assert_eq!(ent.value(), make_value(i).as_slice());
    if i != N - 1 {
      ent = it.next().unwrap();
    }
  }

  assert!(it.next().is_none());
}

pub(crate) fn range_next<M>(l: M)
where
  M: Map + Clone,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  const N: usize = 100;

  for i in (0..N).rev() {
    l.get_or_insert(make_int_key(i).as_slice(), make_value(i).as_slice())
      .unwrap();
  }

  let upper = make_int_key(50);
  let mut i = 0;
  let mut it = l.range(..=upper.as_slice());
  for ent in &mut it {
    assert_eq!(ent.key(), make_int_key(i).as_slice());
    assert_eq!(ent.value(), make_value(i).as_slice());
    i += 1;
  }

  assert_eq!(i, 51);
}

pub(crate) fn iter_with_tombstone_prev<M>(l: M)
where
  M: Map + Clone,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(make_int_key(i).as_slice(), make_value(i).as_slice())
      .unwrap();
  }

  let mut it = l.iter();
  let mut ent = it.seek_upper_bound::<[u8]>(Bound::Unbounded).unwrap();
  for i in (0..N).rev() {
    assert_eq!(ent.key(), make_int_key(i).as_slice());
    assert_eq!(ent.value(), make_value(i).as_slice());
    if i != 0 {
      ent = it.next_back().unwrap();
    }
  }

  assert!(it.next_back().is_none());
}

pub(crate) fn range_prev<M>(l: M)
where
  M: Map + Clone,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(make_int_key(i).as_slice(), make_value(i).as_slice())
      .unwrap();
  }

  let lower = make_int_key(50);
  let it = l.range(lower.as_slice()..);
  let mut i = 99;
  for ent in it.rev() {
    assert_eq!(ent.key(), make_int_key(i).as_slice());
    assert_eq!(ent.value(), make_value(i).as_slice());
    i -= 1;
  }
}

pub(crate) fn iter_with_tombstone_seek_ge<M>(l: M)
where
  M: Map + Clone,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  const N: usize = 100;

  for i in (0..N).rev() {
    let v = i * 10 + 1000;
    l.get_or_insert(make_int_key(v).as_slice(), make_value(v).as_slice())
      .unwrap();
  }

  let mut it = l.iter();
  let ent = it.seek_lower_bound(Bound::Included(b"")).unwrap();
  assert_eq!(ent.key(), make_int_key(1000).as_slice());
  assert_eq!(ent.value(), make_value(1000).as_slice());

  let ent = it.seek_lower_bound(Bound::Included(b"01000")).unwrap();
  assert_eq!(ent.key(), make_int_key(1000).as_slice());
  assert_eq!(ent.value(), make_value(1000).as_slice());

  let ent = it.seek_lower_bound(Bound::Included(b"01005")).unwrap();
  assert_eq!(ent.key(), make_int_key(1010).as_slice());
  assert_eq!(ent.value(), make_value(1010).as_slice());

  let ent = it.seek_lower_bound(Bound::Included(b"01010")).unwrap();
  assert_eq!(ent.key(), make_int_key(1010).as_slice());
  assert_eq!(ent.value(), make_value(1010).as_slice());

  let ent = it.seek_lower_bound(Bound::Included(b"01020")).unwrap();
  assert_eq!(ent.key(), make_int_key(1020).as_slice());
  assert_eq!(ent.value(), make_value(1020).as_slice());

  let ent = it.seek_lower_bound(Bound::Included(b"01200")).unwrap();
  assert_eq!(ent.key(), make_int_key(1200).as_slice());
  assert_eq!(ent.value(), make_value(1200).as_slice());

  let ent = it.seek_lower_bound(Bound::Included(b"01100")).unwrap();
  assert_eq!(ent.key(), make_int_key(1100).as_slice());
  assert_eq!(ent.value(), make_value(1100).as_slice());

  let ent = it.seek_lower_bound(Bound::Included(b"99999"));
  assert!(ent.is_none());

  l.get_or_insert([].as_slice(), [].as_slice()).unwrap();
  let ent = it.seek_lower_bound(Bound::Included(b"")).unwrap();
  assert_eq!(ent.key(), &[]);
  assert_eq!(ent.value(), &[]);

  let ent = it.seek_lower_bound(Bound::Included(b"")).unwrap();
  assert_eq!(ent.key(), &[]);
  assert_eq!(ent.value(), &[]);
}

pub(crate) fn iter_with_tombstone_seek_lt<M>(l: M)
where
  M: Map + Clone,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  const N: usize = 100;

  for i in (0..N).rev() {
    let v = i * 10 + 1000;
    l.get_or_insert(make_int_key(v).as_slice(), make_value(v).as_slice())
      .unwrap();
  }

  let mut it = l.iter();
  assert!(it.seek_upper_bound(Bound::Excluded(b"")).is_none());

  let ent = it.seek_upper_bound(Bound::Excluded(b"01000"));
  assert!(ent.is_none());

  let ent = it.seek_upper_bound(Bound::Excluded(b"01001")).unwrap();
  assert_eq!(ent.key(), make_int_key(1000).as_slice());
  assert_eq!(ent.value(), make_value(1000).as_slice());

  let ent = it.seek_upper_bound(Bound::Excluded(b"01991")).unwrap();
  assert_eq!(ent.key(), make_int_key(1990).as_slice());
  assert_eq!(ent.value(), make_value(1990).as_slice());

  let ent = it.seek_upper_bound(Bound::Excluded(b"99999")).unwrap();
  assert_eq!(ent.key(), make_int_key(1990).as_slice());
  assert_eq!(ent.value(), make_value(1990).as_slice());

  l.get_or_insert([].as_slice(), [].as_slice()).unwrap();

  let ent = it.seek_upper_bound(Bound::Excluded(b""));
  assert!(ent.is_none());

  let ent = it.seek_upper_bound(Bound::Excluded(b"\x01")).unwrap();
  assert_eq!(ent.key(), &[]);
  assert_eq!(ent.value(), &[]);
}

pub(crate) fn range<M>(l: M)
where
  M: Map + Clone,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  for i in 1..10 {
    l.get_or_insert(make_int_key(i).as_slice(), make_value(i).as_slice())
      .unwrap();
  }

  let k3 = make_int_key(3);
  let k7 = make_int_key(7);
  let mut it = l.range(k3.as_slice()..k7.as_slice()).clone();
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
    assert_eq!(ent.key(), make_int_key(3).as_slice());
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
  M: Map + Clone,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(make_int_key(i).as_slice(), make_value(i).as_slice())
      .unwrap();
  }

  for i in 50..N {
    l.insert(make_int_key(i).as_slice(), make_value(i + 1000).as_slice())
      .unwrap();
  }

  for i in 0..50 {
    l.insert(make_int_key(i).as_slice(), make_value(i + 1000).as_slice())
      .unwrap();
  }

  let mut it = l.iter();
  let mut num = 0;
  for i in 0..N {
    let ent = it.next().unwrap();
    assert_eq!(ent.key(), make_int_key(i).as_slice());
    assert_eq!(ent.value(), make_value(i + 1000).as_slice());

    num += 1;
  }
  assert_eq!(num, N);
}

pub(crate) fn range_latest<M>(l: M)
where
  M: Map + Clone,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(make_int_key(i).as_slice(), make_value(i).as_slice())
      .unwrap();
  }

  for i in 50..N {
    l.insert(make_int_key(i).as_slice(), make_value(i + 1000).as_slice())
      .unwrap();
  }

  for i in 0..50 {
    l.insert(make_int_key(i).as_slice(), make_value(i + 1000).as_slice())
      .unwrap();
  }

  let mut it = l.range::<[u8], _>(..);
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
  M: Map + Clone,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  use crate::dynamic::Builder;

  unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join(std::format!("{prefix}_reopen_skipmap"));
    let _ = std::fs::remove_file(&p);
    {
      let l = Builder::new()
        .with_create_new(true)
        .with_read(true)
        .with_write(true)
        .with_capacity(ARENA_SIZE as u32)
        .map_mut::<M, _>(&p)
        .unwrap();
      for i in 0..1000 {
        l.get_or_insert(key(i).as_slice(), new_value(i).as_slice())
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
      let ent = l.get(k.as_slice()).unwrap();
      assert_eq!(new_value(i).as_slice(), ent.value());
      assert_eq!(ent.key(), k.as_slice());
    }
  }
}

#[cfg(feature = "memmap")]
pub(crate) fn reopen_mmap2<M>(prefix: &str)
where
  M: Map + Clone,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  use crate::dynamic::Builder;

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
        l.get_or_insert(key(i).as_slice(), new_value(i).as_slice())
          .unwrap();
      }
      l.flush_async().unwrap();

      for i in data {
        let k = key(i);
        let ent = l.get(k.as_slice()).unwrap();
        assert_eq!(new_value(i).as_slice(), ent.value());
        assert_eq!(ent.key(), k.as_slice());
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
      let ent = l.get(k.as_slice()).unwrap();
      assert_eq!(new_value(i).as_slice(), ent.value());
      assert_eq!(ent.key(), k.as_slice());
    }
  }
}

#[cfg(feature = "memmap")]
pub(crate) fn reopen_mmap3<M>(prefix: &str)
where
  M: Map + Clone,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  use crate::dynamic::Builder;

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
        l.get_or_insert(key(i).as_slice(), new_value(i).as_slice())
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
      let ent = l.get(k.as_slice()).unwrap();
      assert_eq!(new_value(i).as_slice(), ent.value());
      assert_eq!(ent.key(), k.as_slice());
    }
  }
}

// reopen multiple skipmaps based on the same allocator
#[cfg(feature = "memmap")]
pub(crate) fn reopen_mmap4<M>(prefix: &str)
where
  M: Map + Clone + Send + Sync + 'static,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  use crate::dynamic::Builder;

  unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join(std::format!("{prefix}_reopen4_skipmap"));
    let header = {
      let l = Builder::new()
        .with_create_new(true)
        .with_read(true)
        .with_write(true)
        .with_capacity(ARENA_SIZE as u32)
        .map_mut::<M, _>(&p)
        .unwrap();
      let l2 = M::create_from_allocator(l.allocator().clone(), Ascend::new()).unwrap();
      let h2 = l2.header().copied().unwrap();
      let t1 = std::thread::spawn(move || {
        for i in 0..500 {
          l.get_or_insert(key(i).as_slice(), new_value(i).as_slice())
            .unwrap();
        }
        l.flush().unwrap();
      });

      let t2 = std::thread::spawn(move || {
        for i in 500..1000 {
          l2.get_or_insert(key(i).as_slice(), new_value(i).as_slice())
            .unwrap();
        }
        l2.flush().unwrap();
      });

      t1.join().unwrap();
      t2.join().unwrap();

      h2
    };

    let l = Builder::new()
      .with_read(true)
      .with_write(true)
      .with_capacity((ARENA_SIZE * 2) as u32)
      .map_mut::<M, _>(&p)
      .unwrap();
    let l2 = M::open_from_allocator(header, l.allocator().clone(), Ascend::new()).unwrap();
    assert_eq!(500, l.len());
    assert_eq!(500, l2.len());

    for i in 0..500 {
      let k = key(i);
      let ent = l.get(k.as_slice()).unwrap();
      assert_eq!(new_value(i).as_slice(), ent.value());
      assert_eq!(ent.key(), k.as_slice());
    }

    for i in 500..1000 {
      let k = key(i);
      let ent = l2.get(k.as_slice()).unwrap();
      assert_eq!(new_value(i).as_slice(), ent.value());
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
  M: Map + Clone,
  <M::Allocator as Sealed>::Node: WithoutVersion,
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
    Ok(encoded_size)
  });

  l.get_or_insert_with_value_builder::<()>(b"alice".as_slice(), vb)
    .unwrap();
}

pub(crate) fn get_or_insert_with<M>(l: M)
where
  M: Map + Clone,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  let alice = Person {
    id: 1,
    name: std::string::String::from("Alice"),
  };

  let encoded_size = alice.encoded_size();

  let kb = KeyBuilder::new(5u8.into(), |key: &mut VacantBuffer<'_>| {
    key.put_slice(b"alice").unwrap();
    Ok(5)
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
    Ok(encoded_size)
  });

  l.get_or_insert_with_builders::<(), ()>(kb, vb).unwrap();
}

pub(crate) fn insert<M>(l: M)
where
  M: Map + Clone,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  let k = 0u64.to_le_bytes();
  for i in 0..100 {
    let v = new_value(i);
    let old = l.insert(k.as_slice(), v.as_slice()).unwrap();
    if let Some(old) = old {
      assert_eq!(old.key(), k.as_slice());
      assert_eq!(old.value(), new_value(i - 1).as_slice());
    }
  }

  let ent = l.get(k.as_slice()).unwrap();
  assert_eq!(ent.key(), k.as_slice());
  assert_eq!(ent.value(), new_value(99).as_slice());
}

pub(crate) fn insert_with_value<M>(l: M)
where
  M: Map + Clone,
  <M::Allocator as Sealed>::Node: WithoutVersion,
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
    Ok(encoded_size)
  });

  l.insert_with_value_builder::<()>(b"alice".as_slice(), vb)
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
    Ok(encoded_size)
  });

  let old = l
    .insert_with_value_builder::<()>(b"alice".as_slice(), vb)
    .unwrap()
    .unwrap();

  assert_eq!(old.key(), b"alice");
  assert!(old.value().starts_with(&alice.id.to_be_bytes()));

  let ent = l.get(b"alice").unwrap();
  assert_eq!(ent.key(), b"alice");
  assert!(ent.value().starts_with(&alice2.id.to_be_bytes()));
}

pub(crate) fn insert_with<M>(l: M)
where
  M: Map + Clone,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  let alice = Person {
    id: 1,
    name: std::string::String::from("Alice"),
  };

  let encoded_size = alice.encoded_size();

  let kb = KeyBuilder::new(5u8.into(), |key: &mut VacantBuffer<'_>| {
    key.put_slice(b"alice").unwrap();
    Ok(5)
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
    Ok(encoded_size)
  });

  l.insert_with_builders::<(), ()>(kb, vb).unwrap();

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
    Ok(encoded_size)
  });
  let old = l.insert_with_builders::<(), ()>(kb, vb).unwrap().unwrap();

  assert_eq!(old.key(), b"alice");
  assert!(old.value().starts_with(&alice.id.to_be_bytes()));

  let ent = l.get(b"alice").unwrap();
  assert_eq!(ent.key(), b"alice");
  assert!(ent.value().starts_with(&alice2.id.to_be_bytes()));
}

pub(crate) fn get_or_remove<M>(l: M)
where
  M: Map + Clone,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  for i in 0..100 {
    let v = new_value(i);
    l.insert(key(i).as_slice(), v.as_slice()).unwrap();
  }

  for i in 0..100 {
    let k = key(i);
    let old = l.get_or_remove(k.as_slice()).unwrap().unwrap();
    assert_eq!(old.key(), k.as_slice());
    assert_eq!(old.value(), new_value(i).as_slice());

    let old = l.get_or_remove(k.as_slice()).unwrap().unwrap();
    assert_eq!(old.key(), k.as_slice());
    assert_eq!(old.value(), new_value(i).as_slice());
  }

  for i in 0..100 {
    let k = key(i);
    let ent = l.get(k.as_slice()).unwrap();
    assert_eq!(ent.key(), k.as_slice());
    assert_eq!(ent.value(), new_value(i).as_slice());
  }
}

pub(crate) fn remove<M>(l: M)
where
  M: Map + Clone,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  for i in 0..100 {
    let v = new_value(i);
    l.insert(key(i).as_slice(), v.as_slice()).unwrap();
  }

  for i in 0..100 {
    let k = key(i);
    // no race, remove should succeed
    let old = l.remove(k.as_slice()).unwrap();
    assert!(old.is_none());

    // key already removed
    let old = l.remove(k.as_slice()).unwrap();
    assert!(old.is_none());
  }

  for i in 0..100 {
    let k = key(i);
    let ent = l.get(k.as_slice());
    assert!(ent.is_none());
  }
}

pub(crate) fn remove2<M>(l: M)
where
  M: Map + Clone,
  <M::Allocator as Sealed>::Node: WithoutVersion,
{
  for i in 0..100 {
    let v = new_value(i);
    l.insert(key(i).as_slice(), v.as_slice()).unwrap();
  }

  for i in 0..100 {
    let k = key(i);
    // not found, remove should succeed
    let old = l.remove(k.as_slice()).unwrap();
    assert!(old.is_none());

    // no-race, remove should succeed
    let old = l.remove(k.as_slice()).unwrap();
    assert!(old.is_none());
  }

  for i in 0..100 {
    let k = key(i);
    let ent = l.get(k.as_slice());
    assert!(ent.is_none());
  }
}

#[macro_export]
#[doc(hidden)]
macro_rules! __dynamic_map_tests {
  ($prefix:literal: $ty:ty) => {
    $crate::__unit_tests!($crate::tests::dynamic::map |$prefix, $ty, $crate::tests::dynamic::TEST_OPTIONS| {
      empty,
      basic,
      #[cfg(not(miri))]
      basic_large,
      get,
      iter_with_tombstone_next,
      range_next,
      iter_with_tombstone_prev,
      range_prev,
      iter_with_tombstone_seek_ge,
      iter_with_tombstone_seek_lt,
      range,
      iter_latest,
      range_latest,
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

    $crate::__unit_tests!($crate::tests::dynamic::map |$prefix, $ty, $crate::tests::dynamic::TEST_FULL_OPTIONS| {
      full,
    });

    #[test]
    #[cfg(feature = "memmap")]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::macro_metavars_in_unsafe)]
    fn reopen() {
      $crate::tests::dynamic::map::reopen_mmap::<$ty>($prefix);
    }

    #[test]
    #[cfg(feature = "memmap")]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::macro_metavars_in_unsafe)]
    fn reopen2() {
      $crate::tests::dynamic::map::reopen_mmap2::<$ty>($prefix);
    }

    #[test]
    #[cfg(feature = "memmap")]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::macro_metavars_in_unsafe)]
    fn reopen3() {
      $crate::tests::dynamic::map::reopen_mmap3::<$ty>($prefix);
    }
  };
  // Support from golang :)
  (go $prefix:literal: $ty:ty => $opts:path) => {
    $crate::__unit_tests!($crate::tests::dynamic::map |$prefix, $ty, $opts| {
      #[cfg(feature = "std")]
      concurrent_basic_two_maps,
      #[cfg(feature = "std")]
      concurrent_basic,
      #[cfg(feature = "std")]
      concurrent_basic2,
      #[cfg(feature = "std")]
      concurrent_one_key,
      #[cfg(feature = "std")]
      concurrent_one_key2,
    });

    #[test]
    #[cfg(feature = "memmap")]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::macro_metavars_in_unsafe)]
    fn reopen4() {
      $crate::tests::dynamic::map::reopen_mmap4::<$ty>($prefix);
    }

    // #[cfg(not(miri))]
    // mod high_compression {
    //   use super::*;

    //   __unit_tests!($crate::tests::map |$prefix, $ty, $crate::tests::TEST_HIGH_COMPRESSION_OPTIONS| {
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

    $crate::__unit_tests!($crate::tests::dynamic::map |$prefix, $ty, $crate::tests::dynamic::BIG_TEST_OPTIONS| {
      #[cfg(all(feature = "std", not(miri)))]
      concurrent_basic_big_values,
    });
  }
}
