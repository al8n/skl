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
#[cfg_attr(miri, ignore)]
fn test_basic_large_testcases_mmap() {
  let l = Arc::new(SkipSet::mmap(ARENA_SIZE, tempfile::tempfile().unwrap(), true).unwrap());
  test_basic_large_testcases_in(l);
}

#[test]
#[cfg_attr(miri, ignore)]
fn test_basic_large_testcases_mmap_anon() {
  let l = Arc::new(SkipSet::mmap_anon(ARENA_SIZE).unwrap());
  test_basic_large_testcases_in(l);
}

#[test]
#[cfg_attr(miri, ignore)]
fn test_concurrent_basic_mmap_anon() {
  test_concurrent_basic_runner(Arc::new(SkipSet::mmap_anon(ARENA_SIZE).unwrap()));
}

fn test_concurrent_basic_runner(l: Arc<SkipSet>) {
  #[cfg(miri)]
  const N: usize = 100;
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

fn test_concurrent_basic_big_values_runner(l: Arc<SkipSet>) {
  #[cfg(miri)]
  const N: usize = 10;
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
fn test_concurrent_basic_big_values() {
  test_concurrent_basic_big_values_runner(Arc::new(SkipSet::new(120 << 20).unwrap()));
}

#[test]
#[cfg_attr(miri, ignore)]
fn test_concurrent_basic_big_values_mmap() {
  test_concurrent_basic_big_values_runner(Arc::new(
    SkipSet::mmap(120 << 20, tempfile::tempfile().unwrap(), true).unwrap(),
  ));
}

#[test]
#[cfg_attr(miri, ignore)]
fn test_concurrent_basic_big_values_mmap_anon() {
  test_concurrent_basic_big_values_runner(Arc::new(SkipSet::mmap_anon(120 << 20).unwrap()));
}
