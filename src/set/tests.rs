use super::*;
use crate::sync::Arc;
use std::format;
use wg::WaitGroup;

const ARENA_SIZE: usize = 1 << 20;

/// Only used for testing

pub fn key(i: usize) -> Vec<u8> {
  format!("{:05}", i).into_bytes()
}

/// Only used for testing
pub fn big_key(i: usize) -> Vec<u8> {
  format!("{:01048576}", i).into_bytes()
}

fn make_int_key(i: usize) -> Vec<u8> {
  format!("{:05}", i).into_bytes()
}

fn empty_in(l: SkipSet) {
  let mut it = l.iter(0);

  assert!(it.first().is_none());
  assert!(it.last().is_none());
  assert!(it.seek_lower_bound(Bound::Included(b"aaa")).is_none());
  assert!(it.seek_upper_bound(Bound::Excluded(b"aaa")).is_none());
  assert!(it.seek_lower_bound(Bound::Excluded(b"aaa")).is_none());
  assert!(it.seek_upper_bound(Bound::Included(b"aaa")).is_none());
  assert!(l.first(0).is_none());
  assert!(l.last(0).is_none());
  assert!(l.ge(0, b"aaa").is_none());
  assert!(l.lt(0, b"aaa").is_none());
  assert!(l.gt(0, b"aaa").is_none());
  assert!(l.le(0, b"aaa").is_none());
  assert!(l.get(0, b"aaa").is_none());
  assert!(!l.contains_key(0, b"aaa"));
}

#[test]
fn test_empty() {
  empty_in(SkipSet::new(1000).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_empty_mmap() {
  empty_in(SkipSet::mmap(1000, tempfile::tempfile().unwrap(), true).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_empty_mmap_anon() {
  empty_in(SkipSet::mmap_anon(1000).unwrap());
}

fn full_in(l: impl FnOnce(usize) -> SkipSet) {
  let l = l(1000);
  let mut found_arena_full = false;

  for i in 0..100 {
    if let Err(e) = l.insert(0, &make_int_key(i)) {
      assert!(matches!(e, Error::Full(_)));
      found_arena_full = true;
      break;
    }
  }

  assert!(found_arena_full);

  let e = l.insert(0, "someval".as_bytes()).unwrap_err();

  assert!(matches!(e, Error::Full(_)));
}

#[test]
fn test_full() {
  full_in(|n| SkipSet::new(n).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_full_mmap() {
  full_in(|n| SkipSet::mmap(n, tempfile::tempfile().unwrap(), true).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_full_mmap_anon() {
  full_in(|n| SkipSet::mmap_anon(n).unwrap());
}

fn basic_in(mut l: SkipSet) {
  // Try adding values.
  l.insert(0, b"key1").unwrap();
  l.insert(0, b"key3").unwrap();
  l.insert(0, b"key2").unwrap();

  {
    let mut it = l.iter(0);
    let ent = it.seek_lower_bound(Bound::Included(b"key1")).unwrap();
    assert_eq!(ent.key(), b"key1");
    assert_eq!(ent.version(), 0);

    let ent = it.seek_lower_bound(Bound::Included(b"key2")).unwrap();
    assert_eq!(ent.key(), b"key2");
    assert_eq!(ent.version(), 0);

    let ent = it.seek_lower_bound(Bound::Included(b"key3")).unwrap();
    assert_eq!(ent.key(), b"key3");
    assert_eq!(ent.version(), 0);
  }

  l.insert(1, "a".as_bytes()).unwrap();
  l.insert(2, "a".as_bytes()).unwrap();

  {
    let mut it = l.iter(2);
    let ent = it.seek_lower_bound(Bound::Included(b"a")).unwrap();
    assert_eq!(ent.key(), b"a");
    assert_eq!(ent.version(), 2);

    let ent = it.next().unwrap();
    assert_eq!(ent.key(), b"key1");
    assert_eq!(ent.version(), 0);
  }

  l.insert(2, "b".as_bytes()).unwrap();
  l.insert(1, "b".as_bytes()).unwrap();

  {
    let mut it = l.iter(2);
    let ent = it.seek_lower_bound(Bound::Included(b"b")).unwrap();
    assert_eq!(ent.key(), b"b");
    assert_eq!(ent.version(), 2);

    let ent = it.next().unwrap();
    assert_eq!(ent.key(), b"key1");
    assert_eq!(ent.version(), 0);
  }

  l.get_or_insert(2, b"b").unwrap().unwrap();

  assert!(l.get_or_insert(2, b"c").unwrap().is_none());

  l.clear();

  {
    let mut it = l.iter(0);
    assert!(it.first().is_none());
    assert!(it.last().is_none());
  }
}

#[test]
fn test_basic() {
  basic_in(SkipSet::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_basic_mmap() {
  basic_in(SkipSet::mmap(ARENA_SIZE, tempfile::tempfile().unwrap(), true).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_basic_mmap_anon() {
  basic_in(SkipSet::mmap_anon(ARENA_SIZE).unwrap());
}

fn get_mvcc(l: SkipSet) {
  l.insert(1, b"a").unwrap();
  l.insert(3, b"a").unwrap();
  l.insert(1, b"c").unwrap();
  l.insert(3, b"c").unwrap();

  let ent = l.get(1, b"a").unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.version(), 1);

  let ent = l.get(2, b"a").unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.version(), 1);

  let ent = l.get(3, b"a").unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.version(), 3);

  let ent = l.get(4, b"a").unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.version(), 3);

  assert!(l.get(0, b"b").is_none());
  assert!(l.get(1, b"b").is_none());
  assert!(l.get(2, b"b").is_none());
  assert!(l.get(3, b"b").is_none());
  assert!(l.get(4, b"b").is_none());

  let ent = l.get(1, b"c").unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.version(), 1);

  let ent = l.get(2, b"c").unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.version(), 1);

  let ent = l.get(3, b"c").unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.version(), 3);

  let ent = l.get(4, b"c").unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.version(), 3);

  assert!(l.get(5, b"d").is_none());
}

#[test]
fn test_get_mvcc() {
  get_mvcc(SkipSet::new(ARENA_SIZE).unwrap());
}

fn gt_in(l: SkipSet) {
  l.insert(1, b"a").unwrap();
  l.insert(3, b"a").unwrap();
  l.insert(1, b"c").unwrap();
  l.insert(3, b"c").unwrap();
  l.insert(5, b"c").unwrap();

  assert!(l.lower_bound(0, Bound::Excluded(b"a")).is_none());
  assert!(l.lower_bound(0, Bound::Excluded(b"b")).is_none());
  assert!(l.lower_bound(0, Bound::Excluded(b"c")).is_none());

  let ent = l.lower_bound(1, Bound::Excluded(b"")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(2, Bound::Excluded(b"")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(3, Bound::Excluded(b"")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(1, Bound::Excluded(b"a")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(2, Bound::Excluded(b"a")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(3, Bound::Excluded(b"a")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(1, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(2, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(3, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(4, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(5, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.version(), 5);

  let ent = l.lower_bound(6, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.version(), 5);

  assert!(l.lower_bound(1, Bound::Excluded(b"c")).is_none());
  assert!(l.lower_bound(2, Bound::Excluded(b"c")).is_none());
  assert!(l.lower_bound(3, Bound::Excluded(b"c")).is_none());
  assert!(l.lower_bound(4, Bound::Excluded(b"c")).is_none());
  assert!(l.lower_bound(5, Bound::Excluded(b"c")).is_none());
  assert!(l.lower_bound(6, Bound::Excluded(b"c")).is_none());
}

#[test]
fn test_gt() {
  gt_in(SkipSet::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_gt_mmap() {
  gt_in(SkipSet::mmap(ARENA_SIZE, tempfile::tempfile().unwrap(), true).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_gt_mmap_anon() {
  gt_in(SkipSet::mmap_anon(ARENA_SIZE).unwrap());
}

fn ge_in(l: SkipSet) {
  l.insert(1, b"a").unwrap();
  l.insert(3, b"a").unwrap();
  l.insert(1, b"c").unwrap();
  l.insert(3, b"c").unwrap();

  assert!(l.lower_bound(0, Bound::Included(b"a")).is_none());
  assert!(l.lower_bound(0, Bound::Included(b"b")).is_none());
  assert!(l.lower_bound(0, Bound::Included(b"c")).is_none());

  let ent = l.lower_bound(1, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(2, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(3, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(4, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(1, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(2, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(3, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(4, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(1, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(2, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(3, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(4, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.version(), 3);

  assert!(l.lower_bound(0, Bound::Included(b"d")).is_none());
  assert!(l.lower_bound(1, Bound::Included(b"d")).is_none());
  assert!(l.lower_bound(2, Bound::Included(b"d")).is_none());
  assert!(l.lower_bound(3, Bound::Included(b"d")).is_none());
  assert!(l.lower_bound(4, Bound::Included(b"d")).is_none());
}

#[test]
fn test_ge() {
  ge_in(SkipSet::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_ge_mmap() {
  ge_in(SkipSet::mmap(ARENA_SIZE, tempfile::tempfile().unwrap(), true).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_ge_mmap_anon() {
  ge_in(SkipSet::mmap_anon(ARENA_SIZE).unwrap());
}

fn le_in(l: SkipSet) {
  l.insert(1, b"a").unwrap();
  l.insert(3, b"a").unwrap();
  l.insert(1, b"c").unwrap();
  l.insert(3, b"c").unwrap();

  assert!(l.upper_bound(0, Bound::Included(b"a")).is_none());
  assert!(l.upper_bound(0, Bound::Included(b"b")).is_none());
  assert!(l.upper_bound(0, Bound::Included(b"c")).is_none());

  let ent = l.upper_bound(1, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");

  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(2, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");

  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(3, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");

  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(4, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");

  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(1, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");

  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(2, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");

  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(3, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");

  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(4, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");

  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(1, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");

  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(2, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");

  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(3, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");

  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(4, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");

  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(1, Bound::Included(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");

  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(2, Bound::Included(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");

  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(3, Bound::Included(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");

  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(4, Bound::Included(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");

  assert_eq!(ent.version(), 3);
}

#[test]
fn test_le() {
  le_in(SkipSet::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_le_mmap() {
  gt_in(SkipSet::mmap(ARENA_SIZE, tempfile::tempfile().unwrap(), true).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_le_mmap_anon() {
  gt_in(SkipSet::mmap_anon(ARENA_SIZE).unwrap());
}

fn lt_in(l: SkipSet) {
  l.insert(1, b"a").unwrap();
  l.insert(3, b"a").unwrap();
  l.insert(1, b"c").unwrap();
  l.insert(3, b"c").unwrap();

  assert!(l.upper_bound(0, Bound::Excluded(b"a")).is_none());
  assert!(l.upper_bound(0, Bound::Excluded(b"b")).is_none());
  assert!(l.upper_bound(0, Bound::Excluded(b"c")).is_none());
  assert!(l.upper_bound(1, Bound::Excluded(b"a")).is_none());
  assert!(l.upper_bound(2, Bound::Excluded(b"a")).is_none());

  let ent = l.upper_bound(1, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");

  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(2, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");

  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(3, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");

  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(4, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");

  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(1, Bound::Excluded(b"c")).unwrap();
  assert_eq!(ent.key(), b"a");

  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(2, Bound::Excluded(b"c")).unwrap();
  assert_eq!(ent.key(), b"a");

  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(3, Bound::Excluded(b"c")).unwrap();
  assert_eq!(ent.key(), b"a");

  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(4, Bound::Excluded(b"c")).unwrap();
  assert_eq!(ent.key(), b"a");

  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(1, Bound::Excluded(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");

  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(2, Bound::Excluded(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");

  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(3, Bound::Excluded(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");

  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(4, Bound::Excluded(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");

  assert_eq!(ent.version(), 3);
}

#[test]
fn test_lt() {
  lt_in(SkipSet::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_lt_mmap() {
  lt_in(SkipSet::mmap(ARENA_SIZE, tempfile::tempfile().unwrap(), true).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_lt_mmap_anon() {
  lt_in(SkipSet::mmap_anon(ARENA_SIZE).unwrap());
}

fn test_basic_large_testcases_in(l: Arc<SkipSet>) {
  let n = 1000;

  for i in 0..n {
    l.insert(0, &key(i)).unwrap();
  }

  for i in 0..n {
    let k = key(i);
    let ent = l.get(0, &k).unwrap();
    assert_eq!(ent.version(), 0);
    assert_eq!(ent.key(), k);
  }

  assert_eq!(n, l.len());
}

#[test]
fn test_basic_large_testcases() {
  let l = Arc::new(SkipSet::new(ARENA_SIZE).unwrap());
  test_basic_large_testcases_in(l);
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_basic_large_testcases_mmap() {
  let l = Arc::new(SkipSet::mmap(ARENA_SIZE, tempfile::tempfile().unwrap(), true).unwrap());
  test_basic_large_testcases_in(l);
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_basic_large_testcases_mmap_anon() {
  let l = Arc::new(SkipSet::mmap_anon(ARENA_SIZE).unwrap());
  test_basic_large_testcases_in(l);
}

fn test_concurrent_basic_runner(l: Arc<SkipSet>) {
  #[cfg(miri)]
  const N: usize = 5;
  #[cfg(not(miri))]
  const N: usize = 1000;

  let wg = Arc::new(());
  for i in 0..N {
    let w = wg.clone();
    let l = l.clone();
    std::thread::spawn(move || {
      l.insert(0, &key(i)).unwrap();
      drop(w);
    });
  }
  while Arc::strong_count(&wg) > 1 {}
  for i in 0..N {
    let w = wg.clone();
    let l = l.clone();
    std::thread::spawn(move || {
      let k = key(i);
      assert_eq!(l.get(0, &k).unwrap().key(), key(i), "broken: {i}");
      drop(w);
    });
  }
}

#[test]
fn test_concurrent_basic() {
  let l = Arc::new(SkipSet::new(ARENA_SIZE).unwrap());
  test_concurrent_basic_runner(l);
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_concurrent_basic_mmap() {
  let l = Arc::new(SkipSet::mmap(ARENA_SIZE, tempfile::tempfile().unwrap(), true).unwrap());
  test_concurrent_basic_runner(l);
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_concurrent_basic_mmap_anon() {
  test_concurrent_basic_runner(Arc::new(SkipSet::mmap_anon(ARENA_SIZE).unwrap()));
}

fn test_concurrent_basic_big_keys_runner(l: Arc<SkipSet>) {
  #[cfg(miri)]
  const N: usize = 5;
  #[cfg(not(miri))]
  const N: usize = 100;

  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      l.insert(0, &big_key(i)).unwrap();
    });
  }
  while Arc::strong_count(&l) > 1 {}
  assert_eq!(N, l.len());
  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      let k = big_key(i);
      assert_eq!(l.get(0, &k).unwrap().key(), big_key(i), "broken: {i}");
    });
  }
  while Arc::strong_count(&l) > 1 {}
}

#[test]
#[cfg_attr(miri, ignore)]
fn test_concurrent_basic_big_keys() {
  test_concurrent_basic_big_keys_runner(Arc::new(SkipSet::new(120 << 20).unwrap()));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_concurrent_basic_big_keys_mmap() {
  test_concurrent_basic_big_keys_runner(Arc::new(
    SkipSet::mmap(120 << 20, tempfile::tempfile().unwrap(), true).unwrap(),
  ));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_concurrent_basic_big_keys_mmap_anon() {
  test_concurrent_basic_big_keys_runner(Arc::new(SkipSet::mmap_anon(120 << 20).unwrap()));
}

fn concurrent_one_key(l: Arc<SkipSet>) {
  #[cfg(not(miri))]
  const N: usize = 100;
  #[cfg(miri)]
  const N: usize = 5;

  let wg = WaitGroup::new();
  for _ in 0..N {
    let wg = wg.add(1);
    let l = l.clone();
    std::thread::spawn(move || {
      let _ = l.insert(0, b"thekey");
      wg.done();
    });
  }

  wg.wait();

  let saw_value = Arc::new(AtomicU32::new(0));
  for _ in 0..N {
    let wg = wg.add(1);
    let l = l.clone();
    let saw_value = saw_value.clone();
    std::thread::spawn(move || {
      let mut it = l.iter(0);
      let ent = it.seek_lower_bound(Bound::Included(b"thekey")).unwrap();
      assert_eq!(ent.key(), b"thekey");
      saw_value.fetch_add(1, Ordering::SeqCst);
      wg.done();
    });
  }

  wg.wait();

  assert_eq!(N, saw_value.load(Ordering::SeqCst) as usize);
  assert_eq!(l.len(), 1);
}

#[test]
fn test_concurrent_one_key() {
  concurrent_one_key(Arc::new(SkipSet::new(ARENA_SIZE).unwrap()));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_concurrent_one_key_mmap() {
  concurrent_one_key(Arc::new(
    SkipSet::mmap(ARENA_SIZE, tempfile::tempfile().unwrap(), true).unwrap(),
  ));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_concurrent_one_key_mmap_anon() {
  concurrent_one_key(Arc::new(SkipSet::mmap_anon(ARENA_SIZE).unwrap()));
}

fn iterator_next(l: SkipSet) {
  const N: usize = 100;

  for i in (0..N).rev() {
    l.insert(0, &make_int_key(i)).unwrap();
  }

  let mut it = l.iter(0);
  let mut ent = it.first().unwrap();
  for i in 0..N {
    assert_eq!(ent.key(), make_int_key(i));
    if i != N - 1 {
      ent = it.next().unwrap();
    }
  }

  assert!(it.next().is_none());
}

#[test]
fn test_iterator_next() {
  iterator_next(SkipSet::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iterator_next_mmap() {
  iterator_next(SkipSet::mmap(ARENA_SIZE, tempfile::tempfile().unwrap(), true).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iterator_next_mmap_anon() {
  iterator_next(SkipSet::mmap_anon(ARENA_SIZE).unwrap());
}

fn range_next(l: SkipSet) {
  const N: usize = 100;

  for i in (0..N).rev() {
    l.insert(0, &make_int_key(i)).unwrap();
  }

  let upper = make_int_key(50);
  let mut it = l.range(0, ..=upper.as_slice());
  let mut ent = it.first();
  for i in 0..N {
    if i <= 50 {
      {
        let ent = ent.unwrap();
        assert_eq!(ent.key(), make_int_key(i));
      }
      ent = it.next();
    } else {
      assert!(ent.is_none());
      ent = it.next();
    }
  }

  assert!(it.next().is_none());
}

#[test]
fn test_range_next() {
  range_next(SkipSet::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_range_next_mmap() {
  iterator_next(SkipSet::mmap(ARENA_SIZE, tempfile::tempfile().unwrap(), true).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_range_next_mmap_anon() {
  iterator_next(SkipSet::mmap_anon(ARENA_SIZE).unwrap());
}

fn iterator_prev(l: SkipSet) {
  const N: usize = 100;

  for i in 0..N {
    l.insert(0, &make_int_key(i)).unwrap();
  }

  let mut it = l.iter(0);
  let mut ent = it.last().unwrap();
  for i in (0..N).rev() {
    assert_eq!(ent.key(), make_int_key(i));

    if i != 0 {
      ent = it.prev().unwrap();
    }
  }

  assert!(it.prev().is_none());
}

#[test]
fn test_iterator_prev() {
  iterator_prev(SkipSet::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iterator_prev_mmap() {
  iterator_prev(SkipSet::mmap(ARENA_SIZE, tempfile::tempfile().unwrap(), true).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iterator_prev_mmap_anon() {
  iterator_prev(SkipSet::mmap_anon(ARENA_SIZE).unwrap());
}

fn range_prev(l: SkipSet) {
  const N: usize = 100;

  for i in 0..N {
    l.insert(0, &make_int_key(i)).unwrap();
  }

  let lower = make_int_key(50);
  let mut it = l.range(0, lower.as_slice()..);
  let mut ent = it.last();
  for i in (0..N).rev() {
    if i >= 50 {
      {
        let ent = ent.unwrap();
        assert_eq!(ent.key(), make_int_key(i));
      }
      ent = it.prev();
    } else {
      assert!(ent.is_none());
      ent = it.prev();
    }
  }

  assert!(it.prev().is_none());
}

#[test]
fn test_range_prev() {
  range_prev(SkipSet::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_range_prev_mmap() {
  range_prev(SkipSet::mmap(ARENA_SIZE, tempfile::tempfile().unwrap(), true).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_range_prev_mmap_anon() {
  range_prev(SkipSet::mmap_anon(ARENA_SIZE).unwrap());
}

fn iterator_seek_ge(l: SkipSet) {
  const N: usize = 100;

  for i in (0..N).rev() {
    let v = i * 10 + 1000;
    l.insert(0, &make_int_key(v)).unwrap();
  }

  let mut it = l.iter(0);
  let ent = it.seek_lower_bound(Bound::Included(b"")).unwrap();
  assert_eq!(ent.key(), make_int_key(1000));

  let ent = it.seek_lower_bound(Bound::Included(b"01000")).unwrap();
  assert_eq!(ent.key(), make_int_key(1000));

  let ent = it.seek_lower_bound(Bound::Included(b"01005")).unwrap();
  assert_eq!(ent.key(), make_int_key(1010));

  let ent = it.seek_lower_bound(Bound::Included(b"01010")).unwrap();
  assert_eq!(ent.key(), make_int_key(1010));

  let ent = it.seek_lower_bound(Bound::Included(b"01020")).unwrap();
  assert_eq!(ent.key(), make_int_key(1020));

  let ent = it.seek_lower_bound(Bound::Included(b"01200")).unwrap();
  assert_eq!(ent.key(), make_int_key(1200));

  let ent = it.seek_lower_bound(Bound::Included(b"01100")).unwrap();
  assert_eq!(ent.key(), make_int_key(1100));

  let ent = it.seek_lower_bound(Bound::Included(b"99999"));
  assert!(ent.is_none());

  l.insert(0, &[]).unwrap();
  let ent = it.seek_lower_bound(Bound::Included(b"")).unwrap();
  assert_eq!(ent.key(), &[]);

  let ent = it.seek_lower_bound(Bound::Included(b"")).unwrap();
  assert_eq!(ent.key(), &[]);
}

#[test]
fn test_iterator_seek_ge() {
  iterator_seek_ge(SkipSet::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iterator_seek_ge_mmap() {
  iterator_seek_ge(SkipSet::mmap(ARENA_SIZE, tempfile::tempfile().unwrap(), true).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iterator_seek_ge_mmap_anon() {
  iterator_seek_ge(SkipSet::mmap_anon(ARENA_SIZE).unwrap());
}

fn iterator_seek_lt(l: SkipSet) {
  const N: usize = 100;

  for i in (0..N).rev() {
    let v = i * 10 + 1000;
    l.insert(0, &make_int_key(v)).unwrap();
  }

  let mut it = l.iter(0);
  assert!(it.seek_upper_bound(Bound::Excluded(b"")).is_none());

  let ent = it.seek_upper_bound(Bound::Excluded(b"01000"));
  assert!(ent.is_none());

  let ent = it.seek_upper_bound(Bound::Excluded(b"01001")).unwrap();
  assert_eq!(ent.key(), make_int_key(1000));

  let ent = it.seek_upper_bound(Bound::Excluded(b"01991")).unwrap();
  assert_eq!(ent.key(), make_int_key(1990));

  let ent = it.seek_upper_bound(Bound::Excluded(b"99999")).unwrap();
  assert_eq!(ent.key(), make_int_key(1990));

  l.insert(0, &[]).unwrap();
  assert!(l.lt(0, &[]).is_none());

  let ent = it.seek_upper_bound(Bound::Excluded(b""));
  assert!(ent.is_none());

  let ent = it.seek_upper_bound(Bound::Excluded(b"\x01")).unwrap();
  assert_eq!(ent.key(), &[]);
}

#[test]
fn test_iterator_seek_lt() {
  iterator_seek_lt(SkipSet::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iterator_seek_lt_mmap() {
  iterator_seek_lt(SkipSet::mmap(ARENA_SIZE, tempfile::tempfile().unwrap(), true).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iterator_seek_lt_mmap_anon() {
  iterator_seek_lt(SkipSet::mmap_anon(ARENA_SIZE).unwrap());
}

fn range(l: SkipSet) {
  for i in 1..10 {
    l.insert(0, &make_int_key(i)).unwrap();
  }

  let k3 = make_int_key(3);
  let k7 = make_int_key(7);
  let mut it = l.range(0, k3.as_slice()..k7.as_slice());

  for i in 3..=6 {
    let k = make_int_key(i);
    let ent = it.seek_lower_bound(Bound::Included(&k)).unwrap();
    assert_eq!(ent.key(), make_int_key(i));
  }

  for i in 1..3 {
    let k = make_int_key(i);
    let ent = it.seek_lower_bound(Bound::Included(&k)).unwrap();
    assert_eq!(ent.key(), make_int_key(3));
  }

  for i in 7..10 {
    let k = make_int_key(i);
    assert!(it.seek_lower_bound(Bound::Included(&k)).is_none());
  }

  for i in 7..10 {
    let k = make_int_key(i);
    let ent = it.seek_upper_bound(Bound::Included(&k)).unwrap();
    assert_eq!(ent.key(), make_int_key(6));
  }

  let ent = it
    .seek_lower_bound(Bound::Included(&make_int_key(6)))
    .unwrap();
  assert_eq!(ent.key(), make_int_key(6));

  assert!(it.next().is_none());

  let ent = it
    .seek_upper_bound(Bound::Included(&make_int_key(6)))
    .unwrap();
  assert_eq!(ent.key(), make_int_key(6));

  assert!(it.next().is_none());

  for i in 4..=7 {
    let k = make_int_key(i);
    let ent = it.seek_upper_bound(Bound::Excluded(&k)).unwrap();
    assert_eq!(ent.key(), make_int_key(i - 1));
  }

  for i in 7..10 {
    let k = make_int_key(i);
    let ent = it.seek_upper_bound(Bound::Excluded(&k)).unwrap();
    assert_eq!(ent.key(), make_int_key(6));
  }

  for i in 1..3 {
    let k = make_int_key(i);
    let ent = it.seek_lower_bound(Bound::Excluded(&k)).unwrap();
    assert_eq!(ent.key(), make_int_key(3));
  }

  for i in 1..4 {
    let k = make_int_key(i);
    assert!(it.seek_upper_bound(Bound::Excluded(&k)).is_none());
  }

  let ent = it
    .seek_upper_bound(Bound::Excluded(&make_int_key(4)))
    .unwrap();
  assert_eq!(ent.key(), make_int_key(3));
  assert!(it.prev().is_none());
}

#[test]
fn test_range() {
  range(SkipSet::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_range_mmap() {
  range(SkipSet::mmap(ARENA_SIZE, tempfile::tempfile().unwrap(), true).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_range_mmap_anon() {
  range(SkipSet::mmap_anon(ARENA_SIZE).unwrap());
}
