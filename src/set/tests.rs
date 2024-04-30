use wg::WaitGroup;

use super::*;
use crate::sync::Arc;
use std::format;

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
  assert!(it.seek_ge(b"aaa").is_none());
  assert!(it.seek_lt(b"aaa").is_none());
  assert!(it.seek_gt(b"aaa").is_none());
  assert!(it.seek_le(b"aaa").is_none());
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

fn basic_in(l: SkipSet) {
  // Try adding values.
  l.insert(0, b"key1").unwrap();
  l.insert(0, b"key3").unwrap();
  l.insert(0, b"key2").unwrap();

  {
    let mut it = l.iter(0);
    let ent = it.seek_ge(b"key1").unwrap();
    assert_eq!(ent.key(), b"key1");
    assert_eq!(ent.version(), 0);

    let ent = it.seek_ge(b"key2").unwrap();
    assert_eq!(ent.key(), b"key2");
    assert_eq!(ent.version(), 0);

    let ent = it.seek_ge(b"key3").unwrap();
    assert_eq!(ent.key(), b"key3");
    assert_eq!(ent.version(), 0);
  }

  l.insert(1, "a".as_bytes()).unwrap();
  l.insert(2, "a".as_bytes()).unwrap();

  {
    let mut it = l.iter(2);
    let ent = it.seek_ge(b"a").unwrap();
    assert_eq!(ent.key(), b"a");
    assert_eq!(ent.version(), 2);

    let ent = it.next().unwrap();
    assert_eq!(ent.key(), b"a");
    assert_eq!(ent.version(), 1);
  }

  l.insert(2, "b".as_bytes()).unwrap();
  l.insert(1, "b".as_bytes()).unwrap();

  {
    let mut it = l.iter(2);
    let ent = it.seek_ge(b"b").unwrap();
    assert_eq!(ent.key(), b"b");
    assert_eq!(ent.version(), 2);

    let ent = it.next().unwrap();
    assert_eq!(ent.key(), b"b");
    assert_eq!(ent.version(), 1);
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

fn test_basic_large_testcases_in(l: Arc<SkipSet>) {
  let n = 1000;

  for i in 0..n {
    let k = key(i);
    l.insert(0, &k).unwrap();
  }

  for i in 0..n {
    let k = key(i);
    let ent = l.get(0, &k).unwrap();
    assert_eq!(ent.key(), k);
    assert_eq!(ent.version(), 0);
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
      assert_eq!(l.get(0, &k).unwrap().key(), k, "broken: {i}");
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
      assert_eq!(l.get(0, &k).unwrap().key(), k, "broken: {i}");
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
      let ent = l.get(0, b"thekey").unwrap();
      assert_eq!(ent.key(), b"thekey");

      let mut it = l.iter(0);
      let ent = it.seek_ge(b"thekey").unwrap();
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
