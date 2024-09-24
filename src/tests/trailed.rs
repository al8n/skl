use core::sync::atomic::Ordering;

use dbutils::buffer::VacantBuffer;

use crate::{allocator::WithTrailer, trailed::TrailedMap, KeyBuilder, ValueBuilder};

use super::*;

pub(crate) fn basic<M>(mut l: M)
where
  M: TrailedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
  <M::Allocator as Sealed>::Trailer: Default,
{
  // Try adding values.
  l.get_or_insert(b"key1", &make_value(1), Default::default())
    .unwrap();
  l.get_or_insert(b"key3", &make_value(3), Default::default())
    .unwrap();
  l.get_or_insert(b"key2", &make_value(2), Default::default())
    .unwrap();

  {
    let mut it = l.iter();
    let ent = it.seek_lower_bound(Bound::Included(b"key1")).unwrap();
    assert_eq!(ent.key(), b"key1");
    assert_eq!(ent.value(), &make_value(1));

    let ent = it.seek_lower_bound(Bound::Included(b"key2")).unwrap();
    assert_eq!(ent.key(), b"key2");
    assert_eq!(ent.value(), &make_value(2));

    let ent = it.seek_lower_bound(Bound::Included(b"key3")).unwrap();
    assert_eq!(ent.key(), b"key3");
    assert_eq!(ent.value(), &make_value(3));
  }

  l.get_or_insert("a".as_bytes(), &[], Default::default())
    .unwrap();
  l.get_or_insert("a".as_bytes(), &[], Default::default())
    .unwrap();

  {
    let mut it = l.iter();
    let ent = it.seek_lower_bound(Bound::Included(b"a")).unwrap();
    assert_eq!(ent.key(), b"a");
    assert_eq!(ent.value(), &[]);

    let ent = it.next().unwrap();
    assert_eq!(ent.key(), b"key1");
    assert_eq!(ent.value(), &make_value(1));
  }

  l.get_or_insert("b".as_bytes(), &[], Default::default())
    .unwrap();
  l.get_or_insert("b".as_bytes(), &[], Default::default())
    .unwrap();

  {
    let mut it = l.iter();
    let ent = it.seek_lower_bound(Bound::Included(b"b")).unwrap();
    assert_eq!(ent.key(), b"b");
    assert_eq!(ent.value(), &[]);

    let ent = it.next().unwrap();
    assert_eq!(ent.key(), b"key1");
    assert_eq!(ent.value(), &make_value(1));

    let ent = it.entry().unwrap();
    assert_eq!(ent.key(), b"key1");
    assert_eq!(ent.value(), &make_value(1));
  }

  l.get_or_insert(b"b", &[], Default::default())
    .unwrap()
    .unwrap();

  assert!(l
    .get_or_insert(b"c", &[], Default::default())
    .unwrap()
    .is_none());

  unsafe {
    l.clear().unwrap();
  }

  let l = l.clone();
  {
    let mut it = l.iter();
    assert!(it.seek_lower_bound(Bound::Unbounded).is_none());
    assert!(it.seek_upper_bound(Bound::Unbounded).is_none());
  }
  assert!(l.is_empty());

  #[cfg(feature = "memmap")]
  l.flush().unwrap();

  #[cfg(feature = "memmap")]
  l.flush_async().unwrap();
}

pub(crate) fn get<M>(l: M)
where
  M: TrailedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
  <M::Allocator as Sealed>::Trailer: Default,
{
  l.get_or_insert(b"a", b"a1", Default::default()).unwrap();
  l.get_or_insert(b"a", b"a2", Default::default()).unwrap();
  l.get_or_insert(b"c", b"c1", Default::default()).unwrap();
  l.get_or_insert(b"c", b"c2", Default::default()).unwrap();

  let ent = l.get(b"a").unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");

  let ent = l.get(b"a").unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");

  let ent = l.get(b"a").unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");

  l.insert(b"a", b"a2", Default::default()).unwrap();

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
  M: TrailedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
  <M::Allocator as Sealed>::Trailer: Default,
{
  l.get_or_insert(b"a", b"a1", Default::default()).unwrap();
  l.get_or_insert(b"a", b"a2", Default::default()).unwrap();
  l.get_or_insert(b"c", b"c1", Default::default()).unwrap();
  l.get_or_insert(b"c", b"c2", Default::default()).unwrap();
  l.get_or_insert(b"c", b"c3", Default::default()).unwrap();

  assert!(l.lower_bound(Bound::Excluded(b"a")).is_some());
  assert!(l.lower_bound(Bound::Excluded(b"b")).is_some());
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

  let ent = l.lower_bound(Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");

  let ent = l.lower_bound(Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");

  assert!(l.lower_bound(Bound::Excluded(b"c")).is_none());
}

pub(crate) fn ge<M>(l: M)
where
  M: TrailedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
  <M::Allocator as Sealed>::Trailer: Default,
{
  l.get_or_insert(b"a", b"a1", Default::default()).unwrap();
  l.get_or_insert(b"a", b"a2", Default::default()).unwrap();
  l.get_or_insert(b"c", b"c1", Default::default()).unwrap();
  l.get_or_insert(b"c", b"c2", Default::default()).unwrap();

  assert!(l.lower_bound(Bound::Included(b"a")).is_some());
  assert!(l.lower_bound(Bound::Included(b"b")).is_some());
  assert!(l.lower_bound(Bound::Included(b"c")).is_some());

  let ent = l.lower_bound(Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");

  let ent = l.lower_bound(Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");

  l.insert(b"a", b"a2", Default::default()).unwrap();

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
  M: TrailedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
  <M::Allocator as Sealed>::Trailer: Default,
{
  l.get_or_insert(b"a", b"a1", Default::default()).unwrap();
  l.get_or_insert(b"a", b"a2", Default::default()).unwrap();
  l.get_or_insert(b"c", b"c1", Default::default()).unwrap();
  l.get_or_insert(b"c", b"c2", Default::default()).unwrap();

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
  M: TrailedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
  <M::Allocator as Sealed>::Trailer: Default,
{
  l.get_or_insert(b"a", b"a1", Default::default()).unwrap();
  l.get_or_insert(b"a", b"a2", Default::default()).unwrap();
  l.get_or_insert(b"c", b"c1", Default::default()).unwrap();
  l.get_or_insert(b"c", b"c2", Default::default()).unwrap();

  assert!(l.upper_bound(Bound::Excluded(b"a")).is_none());
  assert!(l.upper_bound(Bound::Excluded(b"b")).is_some());
  assert!(l.upper_bound(Bound::Excluded(b"c")).is_some());

  let ent = l.upper_bound(Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");

  let ent = l.upper_bound(Bound::Excluded(b"c")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");

  let ent = l.upper_bound(Bound::Excluded(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
}

#[cfg(not(miri))]
pub(crate) fn basic_large<M>(l: M)
where
  M: TrailedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
  <M::Allocator as Sealed>::Trailer: Default,
{
  let n = 1000;

  for i in 0..n {
    l.get_or_insert(&key(i), &new_value(i), Default::default())
      .unwrap();
  }

  for i in 0..n {
    let k = key(i);
    let ent = l.get(&k).unwrap();
    assert_eq!(new_value(i), ent.value());

    assert_eq!(ent.key(), k);
  }

  assert_eq!(n, l.len());
}

#[cfg(all(
  feature = "std",
  any(all(test, not(miri)), all_tests, test_sync_trailed,)
))]
pub(crate) fn concurrent_basic<M>(l: M)
where
  M: TrailedMap + Clone + Send + 'static,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
  <M::Allocator as Sealed>::Trailer: Default,
{
  #[cfg(not(miri))]
  const N: usize = 1000;
  #[cfg(miri)]
  const N: usize = 200;

  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      l.get_or_insert(&key(i), &new_value(i), Default::default())
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
      assert_eq!(l.get(&k).unwrap().value(), new_value(i), "broken: {i}");
    });
  }
  while l.refs() > 1 {
    ::core::hint::spin_loop();
  }
}

#[cfg(all(
  feature = "std",
  any(all(test, not(miri)), all_tests, test_sync_trailed,)
))]
pub(crate) fn concurrent_basic2<M>(l: M)
where
  M: TrailedMap + Clone + Send + 'static,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
  <M::Allocator as Sealed>::Trailer: Default,
{
  #[cfg(not(miri))]
  const N: usize = 1000;
  #[cfg(miri)]
  const N: usize = 200;

  for i in 0..N {
    let l1 = l.clone();
    let l2 = l.clone();
    std::thread::spawn(move || {
      let _ = l1.insert(&key(i), &new_value(i), Default::default());
    });
    std::thread::spawn(move || {
      let _ = l2.insert(&key(i), &new_value(i), Default::default());
    });
  }
  while l.refs() > 1 {
    ::core::hint::spin_loop();
  }
  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      let k = key(i);
      assert_eq!(l.get(&k).unwrap().value(), new_value(i), "broken: {i}");
    });
  }
  while l.refs() > 1 {
    ::core::hint::spin_loop();
  }
}

#[cfg(all(
  all(feature = "std", not(miri)),
  any(all(test, not(miri)), all_tests, test_sync_trailed,)
))]
pub(crate) fn concurrent_basic_big_values<M>(l: M)
where
  M: TrailedMap + Clone + Send + 'static,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
  <M::Allocator as Sealed>::Trailer: Default,
{
  #[cfg(not(miri))]
  const N: usize = 1000;
  #[cfg(miri)]
  const N: usize = 200;

  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      l.get_or_insert(&key(i), &big_value(i), Default::default())
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
      assert_eq!(l.get(&k).unwrap().value(), big_value(i), "broken: {i}");
    });
  }
  while l.refs() > 1 {
    ::core::hint::spin_loop();
  }
}

#[cfg(all(
  feature = "std",
  any(all(test, not(miri)), all_tests, test_sync_trailed,)
))]
pub(crate) fn concurrent_one_key<M>(l: M)
where
  M: TrailedMap + Clone + Send + 'static,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
  <M::Allocator as Sealed>::Trailer: Default,
{
  use std::sync::Arc;

  #[cfg(not(miri))]
  const N: usize = 1000;
  #[cfg(miri)]
  const N: usize = 200;

  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      let _ = l.get_or_insert(b"thekey", &make_value(i), Default::default());
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
  any(all(test, not(miri)), all_tests, test_sync_trailed,)
))]
pub(crate) fn concurrent_one_key2<M>(l: M)
where
  M: TrailedMap + Clone + Send + 'static,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
  <M::Allocator as Sealed>::Trailer: Default,
{
  use std::sync::Arc;

  #[cfg(not(miri))]
  const N: usize = 1000;
  #[cfg(miri)]
  const N: usize = 200;

  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      let _ = l.insert(b"thekey", &make_value(i), Default::default());
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

pub(crate) fn iter_all_versions_next<M>(l: M)
where
  M: TrailedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
  <M::Allocator as Sealed>::Trailer: Default,
{
  const N: usize = 100;

  for i in (0..N).rev() {
    l.get_or_insert(&make_int_key(i), &make_value(i), Default::default())
      .unwrap();
  }

  let mut it = l.iter();
  let mut ent = it.seek_lower_bound(Bound::Unbounded).unwrap();
  for i in 0..N {
    assert_eq!(ent.key(), make_int_key(i));
    assert_eq!(ent.value(), make_value(i));
    if i != N - 1 {
      ent = it.next().unwrap();
    }
  }

  assert!(it.next().is_none());
}

pub(crate) fn range_next<M>(l: M)
where
  M: TrailedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
  <M::Allocator as Sealed>::Trailer: Default,
{
  const N: usize = 100;

  for i in (0..N).rev() {
    l.get_or_insert(&make_int_key(i), &make_value(i), Default::default())
      .unwrap();
  }

  let upper = make_int_key(50);
  let mut it = l.range(..=upper.as_slice());
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
  M: TrailedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
  <M::Allocator as Sealed>::Trailer: Default,
{
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(&make_int_key(i), &make_value(i), Default::default())
      .unwrap();
  }

  let mut it = l.iter();
  let mut ent = it.seek_upper_bound(Bound::Unbounded).unwrap();
  for i in (0..N).rev() {
    assert_eq!(ent.key(), make_int_key(i));
    assert_eq!(ent.value(), make_value(i));
    if i != 0 {
      ent = it.next_back().unwrap();
    }
  }

  assert!(it.next_back().is_none());
}

pub(crate) fn range_prev<M>(l: M)
where
  M: TrailedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
  <M::Allocator as Sealed>::Trailer: Default,
{
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(&make_int_key(i), &make_value(i), Default::default())
      .unwrap();
  }

  let lower = make_int_key(50);
  let mut it = l.range(lower.as_slice()..);
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
  M: TrailedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
  <M::Allocator as Sealed>::Trailer: Default,
{
  const N: usize = 100;

  for i in (0..N).rev() {
    let v = i * 10 + 1000;
    l.get_or_insert(&make_int_key(v), &make_value(v), Default::default())
      .unwrap();
  }

  let mut it = l.iter();
  let ent = it.seek_lower_bound(Bound::Included(b"")).unwrap();
  assert_eq!(ent.key(), make_int_key(1000));
  assert_eq!(ent.value(), make_value(1000));

  let ent = it.seek_lower_bound(Bound::Included(b"01000")).unwrap();
  assert_eq!(ent.key(), make_int_key(1000));
  assert_eq!(ent.value(), make_value(1000));

  let ent = it.seek_lower_bound(Bound::Included(b"01005")).unwrap();
  assert_eq!(ent.key(), make_int_key(1010));
  assert_eq!(ent.value(), make_value(1010));

  let ent = it.seek_lower_bound(Bound::Included(b"01010")).unwrap();
  assert_eq!(ent.key(), make_int_key(1010));
  assert_eq!(ent.value(), make_value(1010));

  let ent = it.seek_lower_bound(Bound::Included(b"01020")).unwrap();
  assert_eq!(ent.key(), make_int_key(1020));
  assert_eq!(ent.value(), make_value(1020));

  let ent = it.seek_lower_bound(Bound::Included(b"01200")).unwrap();
  assert_eq!(ent.key(), make_int_key(1200));
  assert_eq!(ent.value(), make_value(1200));

  let ent = it.seek_lower_bound(Bound::Included(b"01100")).unwrap();
  assert_eq!(ent.key(), make_int_key(1100));
  assert_eq!(ent.value(), make_value(1100));

  let ent = it.seek_lower_bound(Bound::Included(b"99999"));
  assert!(ent.is_none());

  l.get_or_insert(&[], &[], Default::default()).unwrap();
  let ent = it.seek_lower_bound(Bound::Included(b"")).unwrap();
  assert_eq!(ent.key(), &[]);
  assert_eq!(ent.value(), &[]);

  let ent = it.seek_lower_bound(Bound::Included(b"")).unwrap();
  assert_eq!(ent.key(), &[]);
  assert_eq!(ent.value(), &[]);
}

pub(crate) fn iter_all_versions_seek_lt<M>(l: M)
where
  M: TrailedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
  <M::Allocator as Sealed>::Trailer: Default,
{
  const N: usize = 100;

  for i in (0..N).rev() {
    let v = i * 10 + 1000;
    l.get_or_insert(&make_int_key(v), &make_value(v), Default::default())
      .unwrap();
  }

  let mut it = l.iter();
  assert!(it.seek_upper_bound(Bound::Excluded(b"")).is_none());

  let ent = it.seek_upper_bound(Bound::Excluded(b"01000"));
  assert!(ent.is_none());

  let ent = it.seek_upper_bound(Bound::Excluded(b"01001")).unwrap();
  assert_eq!(ent.key(), make_int_key(1000));
  assert_eq!(ent.value(), make_value(1000));

  let ent = it.seek_upper_bound(Bound::Excluded(b"01991")).unwrap();
  assert_eq!(ent.key(), make_int_key(1990));
  assert_eq!(ent.value(), make_value(1990));

  let ent = it.seek_upper_bound(Bound::Excluded(b"99999")).unwrap();
  assert_eq!(ent.key(), make_int_key(1990));
  assert_eq!(ent.value(), make_value(1990));

  l.get_or_insert(&[], &[], Default::default()).unwrap();

  let ent = it.seek_upper_bound(Bound::Excluded(b""));
  assert!(ent.is_none());

  let ent = it.seek_upper_bound(Bound::Excluded(b"\x01")).unwrap();
  assert_eq!(ent.key(), &[]);
  assert_eq!(ent.value(), &[]);
}

pub(crate) fn range<M>(l: M)
where
  M: TrailedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
  <M::Allocator as Sealed>::Trailer: Default,
{
  for i in 1..10 {
    l.get_or_insert(&make_int_key(i), &make_value(i), Default::default())
      .unwrap();
  }

  let k3 = make_int_key(3);
  let k7 = make_int_key(7);
  let mut it = l.range(k3.as_slice()..k7.as_slice()).clone();
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
  M: TrailedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
  <M::Allocator as Sealed>::Trailer: Default,
{
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(&make_int_key(i), &make_value(i), Default::default())
      .unwrap();
  }

  for i in 50..N {
    l.insert(&make_int_key(i), &make_value(i + 1000), Default::default())
      .unwrap();
  }

  for i in 0..50 {
    l.insert(&make_int_key(i), &make_value(i + 1000), Default::default())
      .unwrap();
  }

  let mut it = l.iter();
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
  M: TrailedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
  <M::Allocator as Sealed>::Trailer: Default,
{
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(&make_int_key(i), &make_value(i), Default::default())
      .unwrap();
  }

  for i in 50..N {
    l.insert(&make_int_key(i), &make_value(i + 1000), Default::default())
      .unwrap();
  }

  for i in 0..50 {
    l.insert(&make_int_key(i), &make_value(i + 1000), Default::default())
      .unwrap();
  }

  let mut it = l.range::<[u8], _>(..);
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
  M: TrailedMap<Comparator = dbutils::Ascend> + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
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
        l.get_or_insert(&key(i), &new_value(i), Default::default())
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
      let ent = l.get(&k).unwrap();
      assert_eq!(new_value(i), ent.value());
      assert_eq!(ent.key(), k);
    }
  }
}

#[cfg(feature = "memmap")]
pub(crate) fn reopen_mmap2<M>(prefix: &str)
where
  M: TrailedMap<Comparator = dbutils::Ascend> + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
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
        l.get_or_insert(&key(i), &new_value(i), Default::default())
          .unwrap();
      }
      l.flush_async().unwrap();

      for i in data {
        let k = key(i);
        let ent = l.get(&k).unwrap();
        assert_eq!(new_value(i), ent.value());
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
      let ent = l.get(&k).unwrap();
      assert_eq!(new_value(i), ent.value());
      assert_eq!(ent.key(), k);
    }
  }
}

#[cfg(feature = "memmap")]
pub(crate) fn reopen_mmap3<M>(prefix: &str)
where
  M: TrailedMap<Comparator = dbutils::Ascend> + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
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
        l.get_or_insert(&key(i), &new_value(i), Default::default())
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
      let ent = l.get(&k).unwrap();
      assert_eq!(new_value(i), ent.value());
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
  M: TrailedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
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

  l.get_or_insert_with_value_builder::<()>(b"alice", vb, Default::default())
    .unwrap();
}

pub(crate) fn get_or_insert_with<M>(l: M)
where
  M: TrailedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
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

  l.get_or_insert_with_builders::<(), ()>(kb, vb, Default::default())
    .unwrap();
}

pub(crate) fn insert<M>(l: M)
where
  M: TrailedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
  <M::Allocator as Sealed>::Trailer: Default,
{
  let k = 0u64.to_le_bytes();
  for i in 0..100 {
    let v = new_value(i);
    let old = l.insert(&k, &v, Default::default()).unwrap();
    if let Some(old) = old {
      assert_eq!(old.key(), k);
      assert_eq!(old.value(), new_value(i - 1));
    }
  }

  let ent = l.get(&k).unwrap();
  assert_eq!(ent.key(), k);
  assert_eq!(ent.value(), new_value(99));
}

pub(crate) fn insert_with_value<M>(l: M)
where
  M: TrailedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
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

  l.insert_with_value_builder::<()>(b"alice", vb, Default::default())
    .unwrap();

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
    .insert_with_value_builder::<()>(b"alice", vb, Default::default())
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
  M: TrailedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
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

  l.insert_with_builders::<(), ()>(kb, vb, Default::default())
    .unwrap();

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
    .insert_with_builders::<(), ()>(kb, vb, Default::default())
    .unwrap()
    .unwrap();

  assert_eq!(old.key(), b"alice");
  assert!(old.value().starts_with(&alice.id.to_be_bytes()));

  let ent = l.get(b"alice").unwrap();
  assert_eq!(ent.key(), b"alice");
  assert!(ent.value().starts_with(&alice2.id.to_be_bytes()));
}

pub(crate) fn get_or_remove<M>(l: M)
where
  M: TrailedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
  <M::Allocator as Sealed>::Trailer: Default,
{
  for i in 0..100 {
    let v = new_value(i);
    l.insert(&key(i), &v, Default::default()).unwrap();
  }

  for i in 0..100 {
    let k = key(i);
    let old = l.get_or_remove(&k, Default::default()).unwrap().unwrap();
    assert_eq!(old.key(), k);
    assert_eq!(old.value(), new_value(i));

    let old = l.get_or_remove(&k, Default::default()).unwrap().unwrap();
    assert_eq!(old.key(), k);
    assert_eq!(old.value(), new_value(i));
  }

  for i in 0..100 {
    let k = key(i);
    let ent = l.get(&k).unwrap();
    assert_eq!(ent.key(), k);
    assert_eq!(ent.value(), new_value(i));
  }
}

pub(crate) fn remove<M>(l: M)
where
  M: TrailedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
  <M::Allocator as Sealed>::Trailer: Default,
{
  for i in 0..100 {
    let v = new_value(i);
    l.insert(&key(i), &v, Default::default()).unwrap();
  }

  for i in 0..100 {
    let k = key(i);
    // no race, remove should succeed
    let old = l.remove(&k, Default::default()).unwrap();
    assert!(old.is_none());

    // key already removed
    let old = l.remove(&k, Default::default()).unwrap();
    assert!(old.is_none());
  }

  for i in 0..100 {
    let k = key(i);
    let ent = l.get(&k);
    assert!(ent.is_none());
  }
}

pub(crate) fn remove2<M>(l: M)
where
  M: TrailedMap + Clone,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Node: WithTrailer,
  <M::Allocator as Sealed>::Trailer: Default,
{
  for i in 0..100 {
    let v = new_value(i);
    l.insert(&key(i), &v, Default::default()).unwrap();
  }

  for i in 0..100 {
    let k = key(i);
    // not found, remove should succeed
    let old = l.remove(&k, Default::default()).unwrap();
    assert!(old.is_none());

    // no-race, remove should succeed
    let old = l.remove(&k, Default::default()).unwrap();
    assert!(old.is_none());
  }

  for i in 0..100 {
    let k = key(i);
    let ent = l.get(&k);
    assert!(ent.is_none());
  }
}

#[macro_export]
#[doc(hidden)]
macro_rules! __trailed_map_tests {
  ($prefix:literal: $ty:ty) => {
    __unit_tests!($crate::tests::trailed |$prefix, $ty, $crate::tests::TEST_OPTIONS| {
      basic,
      #[cfg(not(miri))]
      basic_large,
      get,
      iter_all_versions_next,
      range_next,
      iter_all_versions_prev,
      range_prev,
      iter_all_versions_seek_ge,
      iter_all_versions_seek_lt,
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

    #[test]
    #[cfg(feature = "memmap")]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::macro_metavars_in_unsafe)]
    fn reopen() {
      $crate::tests::trailed::reopen_mmap::<$ty>($prefix);
    }

    #[test]
    #[cfg(feature = "memmap")]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::macro_metavars_in_unsafe)]
    fn reopen2() {
      $crate::tests::trailed::reopen_mmap2::<$ty>($prefix);
    }

    #[test]
    #[cfg(feature = "memmap")]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::macro_metavars_in_unsafe)]
    fn reopen3() {
      $crate::tests::trailed::reopen_mmap3::<$ty>($prefix);
    }
  };
  // Support from golang :)
  (go $prefix:literal: $ty:ty) => {
    __unit_tests!($crate::tests::trailed |$prefix, $ty, $crate::tests::TEST_OPTIONS| {
      #[cfg(feature = "std")]
      concurrent_basic,
      #[cfg(feature = "std")]
      concurrent_basic2,
      #[cfg(feature = "std")]
      concurrent_one_key,
      #[cfg(feature = "std")]
      concurrent_one_key2,
    });

    mod high_compression {
      use super::*;

      __unit_tests!($crate::tests::trailed |$prefix, $ty, $crate::tests::TEST_HIGH_COMPRESSION_OPTIONS| {
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

    __unit_tests!($crate::tests::trailed |$prefix, $ty, $crate::tests::BIG_TEST_OPTIONS| {
      #[cfg(all(feature = "std", not(miri)))]
      concurrent_basic_big_values,
    });
  }
}
