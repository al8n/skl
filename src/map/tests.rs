use super::*;
use crate::{sync::Arc, Descend};
use std::format;

#[cfg(feature = "std")]
use wg::WaitGroup;

const ARENA_SIZE: usize = 1 << 20;

/// Only used for testing

pub fn key(i: usize) -> std::vec::Vec<u8> {
  format!("{:05}", i).into_bytes()
}

/// Only used for testing
#[cfg(feature = "std")]
pub fn big_value(i: usize) -> std::vec::Vec<u8> {
  format!("{:01048576}", i).into_bytes()
}

/// Only used for testing
pub fn new_value(i: usize) -> std::vec::Vec<u8> {
  format!("{:05}", i).into_bytes()
}

fn make_int_key(i: usize) -> std::vec::Vec<u8> {
  format!("{:05}", i).into_bytes()
}

fn make_value(i: usize) -> std::vec::Vec<u8> {
  format!("v{:05}", i).into_bytes()
}

fn empty_in(l: SkipMap) {
  let mut it = l.iter_all_versions(0);

  assert!(it.seek_lower_bound(Bound::Unbounded).is_none());
  assert!(it.seek_upper_bound(Bound::Unbounded).is_none());
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
  assert!(l.size() > 0);
  assert!(l.capacity() > 0);
  assert_eq!(l.remaining(), l.capacity() - l.size());
}

#[test]
fn test_empty() {
  empty_in(SkipMap::new(1000).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_empty_mmap_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_skipmap_empty_mmap_mut");
  let open_options = OpenOptions::default()
    .create_new(Some(1000))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();

  empty_in(SkipMap::mmap_mut(p, open_options, mmap_options).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_empty_mmap_anon() {
  let mmap_options = MmapOptions::default().len(1000);
  empty_in(SkipMap::mmap_anon(mmap_options).unwrap());
}

fn full_in(l: impl FnOnce(usize) -> SkipMap) {
  let l = l(1000);
  let mut found_arena_full = false;

  let mut full_at = 0;
  for i in 0..100 {
    if let Err(e) = l.get_or_insert(0, &make_int_key(i), &make_value(i)) {
      assert!(matches!(e, Error::Full(_)));
      found_arena_full = true;
      full_at = i;
      break;
    }
  }

  assert!(found_arena_full);

  let e = l
    .get_or_insert(0, &make_int_key(full_at + 1), &make_value(full_at + 1))
    .unwrap_err();

  assert!(matches!(e, Error::Full(_)));
}

#[test]
fn test_full() {
  full_in(|n| SkipMap::new(n).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_full_mmap_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_skipmap_full_mmap_mut");

  full_in(|n| {
    let open_options = OpenOptions::default()
      .create_new(Some(n as u64))
      .read(true)
      .write(true);
    let mmap_options = MmapOptions::default();
    SkipMap::mmap_mut(p, open_options, mmap_options).unwrap()
  });
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_full_mmap_anon() {
  full_in(|n| {
    let mmap_options = MmapOptions::default().len(n);
    SkipMap::mmap_anon(mmap_options).unwrap()
  });
}

fn basic_in(mut l: SkipMap) {
  // Try adding values.
  l.get_or_insert(0, b"key1", &make_value(1)).unwrap();
  l.get_or_insert(0, b"key3", &make_value(3)).unwrap();
  l.get_or_insert(0, b"key2", &make_value(2)).unwrap();
  assert_eq!(l.comparator(), &Ascend);

  {
    let mut it = l.iter_all_versions(0);
    let ent = it.seek_lower_bound(Bound::Included(b"key1")).unwrap();
    assert_eq!(ent.key(), b"key1");
    assert_eq!(ent.value(), &make_value(1));
    assert_eq!(ent.trailer().version(), 0);

    let ent = it.seek_lower_bound(Bound::Included(b"key2")).unwrap();
    assert_eq!(ent.key(), b"key2");
    assert_eq!(ent.value(), &make_value(2));
    assert_eq!(ent.trailer().version(), 0);

    let ent = it.seek_lower_bound(Bound::Included(b"key3")).unwrap();
    assert_eq!(ent.key(), b"key3");
    assert_eq!(ent.value(), &make_value(3));
    assert_eq!(ent.trailer().version(), 0);
  }

  l.get_or_insert(1, "a".as_bytes(), &[]).unwrap();
  l.get_or_insert(2, "a".as_bytes(), &[]).unwrap();

  {
    let mut it = l.iter_all_versions(2);
    let ent = it.seek_lower_bound(Bound::Included(b"a")).unwrap();
    assert_eq!(ent.key(), b"a");
    assert_eq!(ent.value(), &[]);
    assert_eq!(ent.trailer().version(), 2);

    let ent = it.next().unwrap();
    assert_eq!(ent.key(), b"a");
    assert_eq!(ent.value(), &[]);
    assert_eq!(ent.trailer().version(), 1);
  }

  l.get_or_insert(2, "b".as_bytes(), &[]).unwrap();
  l.get_or_insert(1, "b".as_bytes(), &[]).unwrap();

  {
    let mut it = l.iter_all_versions(2);
    let ent = it.seek_lower_bound(Bound::Included(b"b")).unwrap();
    assert_eq!(ent.key(), b"b");
    assert_eq!(ent.value(), &[]);
    assert_eq!(ent.trailer().version(), 2);

    let ent = it.next().unwrap();
    assert_eq!(ent.key(), b"b");
    assert_eq!(ent.value(), &[]);
    assert_eq!(ent.trailer().version(), 1);

    let ent = it.entry().unwrap();
    assert_eq!(ent.key(), b"b");
    assert_eq!(ent.value(), &[]);
    assert_eq!(ent.trailer().version(), 1);
  }

  l.get_or_insert(2, b"b", &[]).unwrap().unwrap();

  assert!(l.get_or_insert(2, b"c", &[]).unwrap().is_none());

  {
    #[allow(clippy::clone_on_copy)]
    let a1 = l.get(1, b"a").unwrap().clone();
    let a2 = l.get(2, b"a").unwrap();
    assert!(a1 > a2);
    assert_ne!(a1, a2);
    let b1 = l.get(1, b"b").unwrap();
    let b2 = l.get(2, b"b").unwrap();
    assert!(b1 > b2);
    assert_ne!(b1, b2);
    let mut arr = [a1, a2, b1, b2];
    arr.sort();
    assert_eq!(arr, [a2, a1, b2, b1]);
  }

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

#[test]
fn test_basic() {
  basic_in(SkipMap::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_basic_mmap_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_skipmap_basic_mmap_mut");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  basic_in(SkipMap::mmap_mut(p, open_options, mmap_options).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_basic_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE);
  basic_in(SkipMap::mmap_anon(mmap_options).unwrap());
}

fn iter_all_versions_mvcc(l: SkipMap) {
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
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = it.seek_upper_bound(Bound::Unbounded).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.trailer().version(), 1);

  let mut it = l.iter_all_versions(2);
  let ent = it.seek_lower_bound(Bound::Unbounded).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = it.seek_upper_bound(Bound::Unbounded).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.trailer().version(), 1);

  let mut it = l.iter_all_versions(3);
  let ent = it.min().unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.trailer().version(), 3);

  let ent = it.max().unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.trailer().version(), 3);

  let ent = it.seek_upper_bound(Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.trailer().version(), 3);

  let ent = it.seek_upper_bound(Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.trailer().version(), 3);

  let ent = it.seek_lower_bound(Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.trailer().version(), 3);

  let ent = it.seek_lower_bound(Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.trailer().version(), 3);
}

#[test]
fn test_iter_all_versions_mvcc() {
  iter_all_versions_mvcc(SkipMap::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iter_all_versions_mvcc_mmap_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir
    .path()
    .join("test_skipmap_iter_all_versions_mvcc_mmap_mut");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  iter_all_versions_mvcc(SkipMap::mmap_mut(p, open_options, mmap_options).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iter_all_versions_mvcc_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE);
  iter_all_versions_mvcc(SkipMap::mmap_anon(mmap_options).unwrap());
}

fn ordering() {
  let l = SkipMap::with_comparator(ARENA_SIZE, Descend).unwrap();

  l.get_or_insert(1, b"a1", b"a1").unwrap();
  l.get_or_insert(2, b"a2", b"a2").unwrap();
  l.get_or_insert(3, b"a3", b"a3").unwrap();

  let mut it = l.iter_all_versions(3);
  for i in (1..=3).rev() {
    let ent = it.next().unwrap();
    assert_eq!(ent.key(), format!("a{i}").as_bytes());
    assert_eq!(ent.value(), format!("a{i}").as_bytes());
  }
}

#[test]
fn test_ordering() {
  ordering();
}

fn get_mvcc(l: SkipMap) {
  l.get_or_insert(1, b"a", b"a1").unwrap();
  l.get_or_insert(3, b"a", b"a2").unwrap();
  l.get_or_insert(1, b"c", b"c1").unwrap();
  l.get_or_insert(3, b"c", b"c2").unwrap();

  let ent = l.get(1, b"a").unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.get(2, b"a").unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.get(3, b"a").unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.trailer().version(), 3);

  let ent = l.get(4, b"a").unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.trailer().version(), 3);

  assert!(l.get(0, b"b").is_none());
  assert!(l.get(1, b"b").is_none());
  assert!(l.get(2, b"b").is_none());
  assert!(l.get(3, b"b").is_none());
  assert!(l.get(4, b"b").is_none());

  let ent = l.get(1, b"c").unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.get(2, b"c").unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.get(3, b"c").unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.trailer().version(), 3);

  let ent = l.get(4, b"c").unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.trailer().version(), 3);

  assert!(l.get(5, b"d").is_none());
}

#[test]
fn test_get_mvcc() {
  get_mvcc(SkipMap::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_get_mvcc_mmap_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_skipmap_get_mvcc_mmap_mut");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  get_mvcc(SkipMap::mmap_mut(p, open_options, mmap_options).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_get_mvcc_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE);
  get_mvcc(SkipMap::mmap_anon(mmap_options).unwrap());
}

fn gt_in(l: SkipMap) {
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
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.lower_bound(2, Bound::Excluded(b"")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.lower_bound(3, Bound::Excluded(b"")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.trailer().version(), 3);

  let ent = l.lower_bound(1, Bound::Excluded(b"a")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.lower_bound(2, Bound::Excluded(b"a")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.lower_bound(3, Bound::Excluded(b"a")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.trailer().version(), 3);

  let ent = l.lower_bound(1, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.lower_bound(2, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.lower_bound(3, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.trailer().version(), 3);

  let ent = l.lower_bound(4, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.trailer().version(), 3);

  let ent = l.lower_bound(5, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c3");
  assert_eq!(ent.trailer().version(), 5);

  let ent = l.lower_bound(6, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c3");
  assert_eq!(ent.trailer().version(), 5);

  assert!(l.lower_bound(1, Bound::Excluded(b"c")).is_none());
  assert!(l.lower_bound(2, Bound::Excluded(b"c")).is_none());
  assert!(l.lower_bound(3, Bound::Excluded(b"c")).is_none());
  assert!(l.lower_bound(4, Bound::Excluded(b"c")).is_none());
  assert!(l.lower_bound(5, Bound::Excluded(b"c")).is_none());
  assert!(l.lower_bound(6, Bound::Excluded(b"c")).is_none());
}

#[test]
fn test_gt() {
  gt_in(SkipMap::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_gt_mmap_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_skipmap_gt_mmap_mut");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  gt_in(SkipMap::mmap_mut(p, open_options, mmap_options).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_gt_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE);
  gt_in(SkipMap::mmap_anon(mmap_options).unwrap());
}

fn ge_in(l: SkipMap) {
  l.get_or_insert(1, b"a", b"a1").unwrap();
  l.get_or_insert(3, b"a", b"a2").unwrap();
  l.get_or_insert(1, b"c", b"c1").unwrap();
  l.get_or_insert(3, b"c", b"c2").unwrap();

  assert!(l.lower_bound(0, Bound::Included(b"a")).is_none());
  assert!(l.lower_bound(0, Bound::Included(b"b")).is_none());
  assert!(l.lower_bound(0, Bound::Included(b"c")).is_none());

  let ent = l.lower_bound(1, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.lower_bound(2, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.lower_bound(3, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.trailer().version(), 3);

  let ent = l.lower_bound(4, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.trailer().version(), 3);

  let ent = l.lower_bound(1, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.lower_bound(2, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.lower_bound(3, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.trailer().version(), 3);

  let ent = l.lower_bound(4, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.trailer().version(), 3);

  let ent = l.lower_bound(1, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.lower_bound(2, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.lower_bound(3, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.trailer().version(), 3);

  let ent = l.lower_bound(4, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.trailer().version(), 3);

  assert!(l.lower_bound(0, Bound::Included(b"d")).is_none());
  assert!(l.lower_bound(1, Bound::Included(b"d")).is_none());
  assert!(l.lower_bound(2, Bound::Included(b"d")).is_none());
  assert!(l.lower_bound(3, Bound::Included(b"d")).is_none());
  assert!(l.lower_bound(4, Bound::Included(b"d")).is_none());
}

#[test]
fn test_ge() {
  ge_in(SkipMap::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_ge_mmap_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_skipmap_ge_mmap_mut");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  ge_in(SkipMap::mmap_mut(p, open_options, mmap_options).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_ge_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE);
  ge_in(SkipMap::mmap_anon(mmap_options).unwrap());
}

fn le_in(l: SkipMap) {
  l.get_or_insert(1, b"a", b"a1").unwrap();
  l.get_or_insert(3, b"a", b"a2").unwrap();
  l.get_or_insert(1, b"c", b"c1").unwrap();
  l.get_or_insert(3, b"c", b"c2").unwrap();

  assert!(l.upper_bound(0, Bound::Included(b"a")).is_none());
  assert!(l.upper_bound(0, Bound::Included(b"b")).is_none());
  assert!(l.upper_bound(0, Bound::Included(b"c")).is_none());

  let ent = l.upper_bound(1, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.upper_bound(2, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.upper_bound(3, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.trailer().version(), 3);

  let ent = l.upper_bound(4, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.trailer().version(), 3);

  let ent = l.upper_bound(1, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.upper_bound(2, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.upper_bound(3, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.trailer().version(), 3);

  let ent = l.upper_bound(4, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.trailer().version(), 3);

  let ent = l.upper_bound(1, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.upper_bound(2, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.upper_bound(3, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.trailer().version(), 3);

  let ent = l.upper_bound(4, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.trailer().version(), 3);

  let ent = l.upper_bound(1, Bound::Included(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.upper_bound(2, Bound::Included(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.upper_bound(3, Bound::Included(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.trailer().version(), 3);

  let ent = l.upper_bound(4, Bound::Included(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.trailer().version(), 3);
}

#[test]
fn test_le() {
  le_in(SkipMap::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_le_mmap_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_skipmap_le_mmap_mut");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  gt_in(SkipMap::mmap_mut(p, open_options, mmap_options).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_le_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE);
  gt_in(SkipMap::mmap_anon(mmap_options).unwrap());
}

fn lt_in(l: SkipMap) {
  l.get_or_insert(1, b"a", b"a1").unwrap();
  l.get_or_insert(3, b"a", b"a2").unwrap();
  l.get_or_insert(1, b"c", b"c1").unwrap();
  l.get_or_insert(3, b"c", b"c2").unwrap();

  assert!(l.upper_bound(0, Bound::Excluded(b"a")).is_none());
  assert!(l.upper_bound(0, Bound::Excluded(b"b")).is_none());
  assert!(l.upper_bound(0, Bound::Excluded(b"c")).is_none());
  assert!(l.upper_bound(1, Bound::Excluded(b"a")).is_none());
  assert!(l.upper_bound(2, Bound::Excluded(b"a")).is_none());

  let ent = l.upper_bound(1, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.upper_bound(2, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.upper_bound(3, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.trailer().version(), 3);

  let ent = l.upper_bound(4, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.trailer().version(), 3);

  let ent = l.upper_bound(1, Bound::Excluded(b"c")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.upper_bound(2, Bound::Excluded(b"c")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.upper_bound(3, Bound::Excluded(b"c")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.trailer().version(), 3);

  let ent = l.upper_bound(4, Bound::Excluded(b"c")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.trailer().version(), 3);

  let ent = l.upper_bound(1, Bound::Excluded(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.upper_bound(2, Bound::Excluded(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.trailer().version(), 1);

  let ent = l.upper_bound(3, Bound::Excluded(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.trailer().version(), 3);

  let ent = l.upper_bound(4, Bound::Excluded(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.trailer().version(), 3);
}

#[test]
fn test_lt() {
  lt_in(SkipMap::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_lt_mmap_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_skipmap_lt_mmap_mut");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  lt_in(SkipMap::mmap_mut(p, open_options, mmap_options).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_lt_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE);
  lt_in(SkipMap::mmap_anon(mmap_options).unwrap());
}

fn test_basic_large_testcases_in(l: Arc<SkipMap>) {
  let n = 1000;

  for i in 0..n {
    l.get_or_insert(0, &key(i), &new_value(i)).unwrap();
  }

  for i in 0..n {
    let k = key(i);
    let ent = l.get(0, &k).unwrap();
    assert_eq!(new_value(i), ent.value());
    assert_eq!(ent.trailer().version(), 0);
    assert_eq!(ent.key(), k);
  }

  assert_eq!(n, l.len());
}

#[test]
fn test_basic_large_testcases() {
  let l = Arc::new(SkipMap::new(ARENA_SIZE).unwrap());
  test_basic_large_testcases_in(l);
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_basic_large_testcases_mmap_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir
    .path()
    .join("test_skipmap_basic_large_testcases_mmap_mut");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  let l = Arc::new(SkipMap::mmap_mut(p, open_options, mmap_options).unwrap());
  test_basic_large_testcases_in(l);
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_basic_large_testcases_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE);
  let l = Arc::new(SkipMap::mmap_anon(mmap_options).unwrap());
  test_basic_large_testcases_in(l);
}

#[cfg(feature = "std")]
fn test_concurrent_basic_runner(l: Arc<SkipMap>) {
  #[cfg(miri)]
  const N: usize = 5;
  #[cfg(not(miri))]
  const N: usize = 1000;

  let wg = Arc::new(());
  for i in 0..N {
    let w = wg.clone();
    let l = l.clone();
    std::thread::spawn(move || {
      l.get_or_insert(0, &key(i), &new_value(i)).unwrap();
      drop(w);
    });
  }
  while Arc::strong_count(&wg) > 1 {}
  for i in 0..N {
    let w = wg.clone();
    let l = l.clone();
    std::thread::spawn(move || {
      let k = key(i);
      assert_eq!(l.get(0, &k).unwrap().value(), new_value(i), "broken: {i}");
      drop(w);
    });
  }
}

#[test]
#[cfg(feature = "std")]
fn test_concurrent_basic() {
  let l = Arc::new(SkipMap::new(ARENA_SIZE).unwrap().with_yield_now());
  test_concurrent_basic_runner(l);
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_concurrent_basic_mmap_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_skipmap_concurrent_basic_mmap_mut");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  let l = Arc::new(
    SkipMap::mmap_mut(p, open_options, mmap_options)
      .unwrap()
      .with_yield_now(),
  );
  test_concurrent_basic_runner(l);
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_concurrent_basic_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE);
  test_concurrent_basic_runner(Arc::new(
    SkipMap::mmap_anon(mmap_options).unwrap().with_yield_now(),
  ));
}

#[cfg(feature = "std")]
fn test_concurrent_basic_big_values_runner(l: Arc<SkipMap>) {
  #[cfg(miri)]
  const N: usize = 5;
  #[cfg(not(miri))]
  const N: usize = 100;

  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      l.get_or_insert(0, &key(i), &big_value(i)).unwrap();
    });
  }
  while Arc::strong_count(&l) > 1 {}
  assert_eq!(N, l.len());
  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      let k = key(i);
      assert_eq!(l.get(0, &k).unwrap().value(), big_value(i), "broken: {i}");
    });
  }
  while Arc::strong_count(&l) > 1 {}
}

#[test]
#[cfg(feature = "std")]
#[cfg_attr(miri, ignore)]
fn test_concurrent_basic_big_values() {
  test_concurrent_basic_big_values_runner(Arc::new(
    SkipMap::new(120 << 20).unwrap().with_yield_now(),
  ));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_concurrent_basic_big_values_mmap_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir
    .path()
    .join("test_skipmap_concurrent_basic_big_values_mmap_mut");
  let open_options = OpenOptions::default()
    .create_new(Some(120 << 20))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  test_concurrent_basic_big_values_runner(Arc::new(
    SkipMap::mmap_mut(p, open_options, mmap_options)
      .unwrap()
      .with_yield_now(),
  ));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_concurrent_basic_big_values_mmap_anon() {
  let mmap_options = MmapOptions::default().len(120 << 20);
  test_concurrent_basic_big_values_runner(Arc::new(
    SkipMap::mmap_anon(mmap_options).unwrap().with_yield_now(),
  ));
}

#[cfg(feature = "std")]
fn concurrent_one_key(l: Arc<SkipMap>) {
  #[cfg(not(miri))]
  const N: usize = 100;
  #[cfg(miri)]
  const N: usize = 5;

  let wg = WaitGroup::new();
  for i in 0..N {
    let wg = wg.add(1);
    let l = l.clone();
    std::thread::spawn(move || {
      let _ = l.get_or_insert(0, b"thekey", &make_value(i));
      wg.done();
    });
  }

  wg.wait();

  let saw_value = Arc::new(crate::sync::AtomicU32::new(0));
  for _ in 0..N {
    let wg = wg.add(1);
    let l = l.clone();
    let saw_value = saw_value.clone();
    std::thread::spawn(move || {
      let ent = l.get(0, b"thekey").unwrap();
      let val = ent.value();
      let num: usize = core::str::from_utf8(&val[1..]).unwrap().parse().unwrap();
      assert!((0..N).contains(&num));

      let mut it = l.iter_all_versions(0);
      let ent = it.seek_lower_bound(Bound::Included(b"thekey")).unwrap();
      let val = ent.value();
      let num: usize = core::str::from_utf8(&val[1..]).unwrap().parse().unwrap();
      assert!((0..N).contains(&num));
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
#[cfg(feature = "std")]
fn test_concurrent_one_key() {
  concurrent_one_key(Arc::new(SkipMap::new(ARENA_SIZE).unwrap().with_yield_now()));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_concurrent_one_key_mmap_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_skipmap_concurrent_one_key_mmap_mut");
  let open_options = OpenOptions::default()
    .create(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true)
    .shrink_on_drop(true);
  let mmap_options = MmapOptions::default();
  concurrent_one_key(Arc::new(
    SkipMap::mmap_mut(p, open_options, mmap_options)
      .unwrap()
      .with_yield_now(),
  ));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_concurrent_one_key_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE);
  concurrent_one_key(Arc::new(
    SkipMap::mmap_anon(mmap_options).unwrap().with_yield_now(),
  ));
}

fn iter_all_versionsator_next(l: SkipMap) {
  const N: usize = 100;

  for i in (0..N).rev() {
    l.get_or_insert(0, &make_int_key(i), &make_value(i))
      .unwrap();
  }

  let mut it = l.iter_all_versions(0);
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

#[test]
fn test_iter_all_versionsator_next() {
  iter_all_versionsator_next(SkipMap::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iter_all_versionsator_next_mmap_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir
    .path()
    .join("test_skipmap_iter_all_versionsator_next_mmap_mut");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  iter_all_versionsator_next(SkipMap::mmap_mut(p, open_options, mmap_options).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iter_all_versionsator_next_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE);
  iter_all_versionsator_next(SkipMap::mmap_anon(mmap_options).unwrap());
}

fn range_next(l: SkipMap) {
  const N: usize = 100;

  for i in (0..N).rev() {
    l.get_or_insert(0, &make_int_key(i), &make_value(i))
      .unwrap();
  }

  let upper = make_int_key(50);
  let mut it = l.range(0, ..=upper.as_slice());
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

#[test]
fn test_range_next() {
  range_next(SkipMap::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_range_next_mmap_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_skipmap_range_next_mmap_mut");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  iter_all_versionsator_next(SkipMap::mmap_mut(p, open_options, mmap_options).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_range_next_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE);
  iter_all_versionsator_next(SkipMap::mmap_anon(mmap_options).unwrap());
}

fn iter_all_versionsator_prev(l: SkipMap) {
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(0, &make_int_key(i), &make_value(i))
      .unwrap();
  }

  let mut it = l.iter_all_versions(0);
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

#[test]
fn test_iter_all_versionsator_next_back() {
  iter_all_versionsator_prev(SkipMap::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iter_all_versionsator_prev_mmap_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir
    .path()
    .join("test_skipmap_iter_all_versionsator_prev_mmap_mut");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  iter_all_versionsator_prev(SkipMap::mmap_mut(p, open_options, mmap_options).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iter_all_versionsator_prev_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE);
  iter_all_versionsator_prev(SkipMap::mmap_anon(mmap_options).unwrap());
}

fn range_prev(l: SkipMap) {
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(0, &make_int_key(i), &make_value(i))
      .unwrap();
  }

  let lower = make_int_key(50);
  let mut it = l.range(0, lower.as_slice()..);
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

#[test]
fn test_range_next_back() {
  range_prev(SkipMap::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_range_prev_mmap_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_skipmap_range_prev_mmap_mut");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  range_prev(SkipMap::mmap_mut(p, open_options, mmap_options).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_range_prev_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE);
  range_prev(SkipMap::mmap_anon(mmap_options).unwrap());
}

fn iter_all_versionsator_seek_ge(l: SkipMap) {
  const N: usize = 100;

  for i in (0..N).rev() {
    let v = i * 10 + 1000;
    l.get_or_insert(0, &make_int_key(v), &make_value(v))
      .unwrap();
  }

  let mut it = l.iter_all_versions(0);
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

  l.get_or_insert(0, &[], &[]).unwrap();
  let ent = it.seek_lower_bound(Bound::Included(b"")).unwrap();
  assert_eq!(ent.key(), &[]);
  assert_eq!(ent.value(), &[]);

  let ent = it.seek_lower_bound(Bound::Included(b"")).unwrap();
  assert_eq!(ent.key(), &[]);
  assert_eq!(ent.value(), &[]);
}

#[test]
fn test_iter_all_versionsator_seek_ge() {
  iter_all_versionsator_seek_ge(SkipMap::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iter_all_versionsator_seek_ge_mmap_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir
    .path()
    .join("test_skipmap_iter_all_versionsator_seek_ge_mmap_mut");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  iter_all_versionsator_seek_ge(SkipMap::mmap_mut(p, open_options, mmap_options).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iter_all_versionsator_seek_ge_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE);
  iter_all_versionsator_seek_ge(SkipMap::mmap_anon(mmap_options).unwrap());
}

fn iter_all_versionsator_seek_lt(l: SkipMap) {
  const N: usize = 100;

  for i in (0..N).rev() {
    let v = i * 10 + 1000;
    l.get_or_insert(0, &make_int_key(v), &make_value(v))
      .unwrap();
  }

  let mut it = l.iter_all_versions(0);
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

  l.get_or_insert(0, &[], &[]).unwrap();
  assert!(l.lt(0, &[]).is_none());

  let ent = it.seek_upper_bound(Bound::Excluded(b""));
  assert!(ent.is_none());

  let ent = it.seek_upper_bound(Bound::Excluded(b"\x01")).unwrap();
  assert_eq!(ent.key(), &[]);
  assert_eq!(ent.value(), &[]);
}

#[test]
fn test_iter_all_versionsator_seek_lt() {
  iter_all_versionsator_seek_lt(SkipMap::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iter_all_versionsator_seek_lt_mmap_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir
    .path()
    .join("test_skipmap_iter_all_versionsator_seek_lt_mmap_mut");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  iter_all_versionsator_seek_lt(SkipMap::mmap_mut(p, open_options, mmap_options).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iter_all_versionsator_seek_lt_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE);
  iter_all_versionsator_seek_lt(SkipMap::mmap_anon(mmap_options).unwrap());
}

fn range(l: SkipMap) {
  for i in 1..10 {
    l.get_or_insert(0, &make_int_key(i), &make_value(i))
      .unwrap();
  }

  let k3 = make_int_key(3);
  let k7 = make_int_key(7);
  let mut it = l.range(0, k3.as_slice()..k7.as_slice()).clone();
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

#[test]
fn test_range() {
  range(SkipMap::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_range_mmap_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_skipmap_range_mmap_mut");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  range(SkipMap::mmap_mut(p, open_options, mmap_options).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_range_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE);
  range(SkipMap::mmap_anon(mmap_options).unwrap());
}

fn iter_latest(l: SkipMap) {
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(0, &make_int_key(i), &make_value(i))
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

#[test]
fn test_iter_latest() {
  iter_latest(SkipMap::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iter_latest_mmap_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_skipmap_iter_latest_mmap_mut");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  iter_latest(SkipMap::mmap_mut(p, open_options, mmap_options).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iter_latest_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE);
  iter_latest(SkipMap::mmap_anon(mmap_options).unwrap());
}

fn range_latest(l: SkipMap) {
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(0, &make_int_key(i), &make_value(i))
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

  let mut it = l.range(4, ..);
  let mut num = 0;
  for i in 0..N {
    let ent = it.next().unwrap();
    assert_eq!(ent.key(), make_int_key(i));
    assert_eq!(ent.value(), make_value(i + 1000));

    num += 1;
  }
  assert_eq!(num, N);
}

#[test]
fn test_range_latest() {
  range_latest(SkipMap::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_range_latest_mmap_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_skipmap_range_latest_mmap_mut");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  range_latest(SkipMap::mmap_mut(p, open_options, mmap_options).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_range_latest_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE);
  range_latest(SkipMap::mmap_anon(mmap_options).unwrap());
}

#[test]
// #[cfg(feature = "memmap")]
// #[cfg_attr(miri, ignore)]
fn test_xxx() {

    let l = SkipMap::new(ARENA_SIZE).unwrap();
    for i in 0..3 {
      l.get_or_insert(0, &key(i), &new_value(i)).unwrap();
    }
    l.flush().unwrap();

  assert_eq!(3, l.len());
  for i in 0..3 {
    let k = key(i);
    println!("{}", i);
    let ent = l.get(0, &k).unwrap();
    assert_eq!(new_value(i), ent.value());
    assert_eq!(ent.trailer().version(), 0);
    assert_eq!(ent.key(), k);
  }
}

#[test]
// #[cfg(feature = "memmap")]
// #[cfg_attr(miri, ignore)]
fn test_reopen_mmap() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("reopen_skipmap");
  {
    let open_options = OpenOptions::default()
      .create(Some(ARENA_SIZE as u64))
      .read(true)
      .write(true)
      .lock_exclusive(true);
    let mmap_options = MmapOptions::default();
    let l = SkipMap::mmap_mut(&p, open_options, mmap_options).unwrap();
    for i in 0..2 {
      l.get_or_insert(0, &key(i), &new_value(i)).unwrap();
    }
    l.flush().unwrap();
  }

  let open_options = OpenOptions::default()
    .read(true)
    .lock_shared(true)
    .shrink_on_drop(true);
  let mmap_options = MmapOptions::default();
  let l = SkipMap::mmap(&p, open_options, mmap_options).unwrap();
  assert_eq!(2, l.len());
  for i in 0..2 {
    let k = key(i);
    println!("{}", i);
    let ent = l.get(0, &k).unwrap();
    assert_eq!(new_value(i), ent.value());
    assert_eq!(ent.trailer().version(), 0);
    assert_eq!(ent.key(), k);
  }
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_reopen_mmap2() {
  use rand::seq::SliceRandom;

  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("reopen_skipmap2");
  {
    let open_options = OpenOptions::default()
      .create(Some(ARENA_SIZE as u64))
      .read(true)
      .write(true)
      .lock_shared(true);
    let mmap_options = MmapOptions::default();
    let l = SkipMap::mmap_mut_with_comparator(&p, open_options, mmap_options, Ascend).unwrap();
    let mut data = (0..1000).collect::<Vec<usize>>();
    data.shuffle(&mut rand::thread_rng());
    for i in data {
      l.get_or_insert(i as u64, &key(i), &new_value(i)).unwrap();
    }
    l.flush_async().unwrap();
    assert_eq!(l.max_version(), 999);
    assert_eq!(l.min_version(), 0);
  }

  let open_options = OpenOptions::default().read(true);
  let mmap_options = MmapOptions::default();
  let l =
    SkipMap::<u64, Ascend>::mmap_with_comparator(&p, open_options, mmap_options, Ascend).unwrap();
  assert_eq!(1000, l.len());
  let mut data = (0..1000).collect::<Vec<usize>>();
  data.shuffle(&mut rand::thread_rng());
  for i in data {
    let k = key(i);
    let ent = l.get(i as u64, &k).unwrap();
    assert_eq!(new_value(i), ent.value());
    assert_eq!(ent.trailer().version(), i as u64);
    assert_eq!(ent.key(), k);
  }
  assert_eq!(l.max_version(), 999);
  assert_eq!(l.min_version(), 0);
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

#[cfg(feature = "std")]
fn get_or_insert_with_panic(l: SkipMap) {
  let alice = Person {
    id: 1,
    name: std::string::String::from("Alice"),
  };

  let encoded_size = alice.encoded_size();

  l.get_or_insert_with::<()>(1, b"alice", encoded_size as u32, |mut val| {
    val.write(&alice.id.to_le_bytes()).unwrap();
    Ok(())
  })
  .unwrap();
}

#[test]
#[cfg(feature = "std")]
#[should_panic]
fn test_get_or_insert_with_panic() {
  get_or_insert_with_panic(SkipMap::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
#[should_panic]
fn test_get_or_insert_with_panic_mmap_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_skipmap_get_or_insert_with_mmap_mut");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  get_or_insert_with_panic(SkipMap::mmap_mut(p, open_options, mmap_options).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
#[should_panic]
fn test_get_or_insert_with_panic_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE);
  get_or_insert_with_panic(SkipMap::mmap_anon(mmap_options).unwrap());
}

fn get_or_insert_with(l: SkipMap) {
  let alice = Person {
    id: 1,
    name: std::string::String::from("Alice"),
  };

  let encoded_size = alice.encoded_size() as u32;

  l.get_or_insert_with::<()>(1, b"alice", encoded_size, |mut val| {
    assert_eq!(val.capacity(), encoded_size as usize);
    assert!(val.is_empty());
    val.write(&alice.id.to_le_bytes()).unwrap();
    assert_eq!(val.len(), 4);
    assert_eq!(val.remaining(), encoded_size as usize - 4);
    assert_eq!(&*val, alice.id.to_le_bytes());
    val[..4].copy_from_slice(&alice.id.to_be_bytes());
    assert_eq!(&*val, alice.id.to_be_bytes());
    val.write(alice.name.as_bytes()).unwrap();
    assert_eq!(val.len(), encoded_size as usize);
    let err = val.write(&[1]).unwrap_err();
    assert_eq!(
      std::string::ToString::to_string(&err),
      "OccupiedValue does not have enough space (remaining 0, want 1)"
    );
    Ok(())
  })
  .unwrap();
}

#[test]
fn test_get_or_insert_with() {
  get_or_insert_with(SkipMap::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_get_or_insert_with_mmap_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_skipmap_get_or_insert_with_mmap_mut");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  get_or_insert_with(SkipMap::mmap_mut(p, open_options, mmap_options).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_get_or_insert_with_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE);
  get_or_insert_with(SkipMap::mmap_anon(mmap_options).unwrap());
}

fn insert_in(l: SkipMap) {
  let k = 0u64.to_le_bytes();
  for i in 0..100 {
    let v = new_value(i);
    let old = l.insert(0, &k, &v).unwrap();
    if let Some(old) = old {
      assert_eq!(old.key(), k);
      assert_eq!(old.value(), new_value(i - 1));
    }
  }

  let ent = l.get(0, &k).unwrap();
  assert_eq!(ent.key(), k);
  assert_eq!(ent.value(), new_value(99));
}

#[test]
fn test_insert_in() {
  insert_in(SkipMap::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_insert_in_mmap_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_skipmap_insert_in_mmap_mut");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  insert_in(SkipMap::mmap_mut(p, open_options, mmap_options).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_insert_in_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE);
  insert_in(SkipMap::mmap_anon(mmap_options).unwrap());
}

fn insert_with(l: SkipMap) {
  let alice = Person {
    id: 1,
    name: std::string::String::from("Alice"),
  };

  let encoded_size = alice.encoded_size() as u32;

  l.insert_with::<()>(1, b"alice", encoded_size, |mut val| {
    assert_eq!(val.capacity(), encoded_size as usize);
    assert!(val.is_empty());
    val.write(&alice.id.to_le_bytes()).unwrap();
    assert_eq!(val.len(), 4);
    assert_eq!(val.remaining(), encoded_size as usize - 4);
    assert_eq!(&*val, alice.id.to_le_bytes());
    val[..4].copy_from_slice(&alice.id.to_be_bytes());
    assert_eq!(&*val, alice.id.to_be_bytes());
    val.write(alice.name.as_bytes()).unwrap();
    assert_eq!(val.len(), encoded_size as usize);
    let err = val.write(&[1]).unwrap_err();
    assert_eq!(
      std::string::ToString::to_string(&err),
      "OccupiedValue does not have enough space (remaining 0, want 1)"
    );
    Ok(())
  })
  .unwrap();

  let alice2 = Person {
    id: 2,
    name: std::string::String::from("Alice"),
  };

  let old = l
    .insert_with::<()>(1, b"alice", encoded_size, |mut val| {
      assert_eq!(val.capacity(), encoded_size as usize);
      assert!(val.is_empty());
      val.write(&alice2.id.to_le_bytes()).unwrap();
      assert_eq!(val.len(), 4);
      assert_eq!(val.remaining(), encoded_size as usize - 4);
      assert_eq!(&*val, alice2.id.to_le_bytes());
      val[..4].copy_from_slice(&alice2.id.to_be_bytes());
      assert_eq!(&*val, alice2.id.to_be_bytes());
      val.write(alice2.name.as_bytes()).unwrap();
      assert_eq!(val.len(), encoded_size as usize);
      let err = val.write(&[1]).unwrap_err();
      assert_eq!(
        std::string::ToString::to_string(&err),
        "OccupiedValue does not have enough space (remaining 0, want 1)"
      );
      Ok(())
    })
    .unwrap()
    .unwrap();

  assert_eq!(old.key(), b"alice");
  assert!(old.value().starts_with(&alice.id.to_be_bytes()));

  let ent = l.get(1, b"alice").unwrap();
  assert_eq!(ent.key(), b"alice");
  assert!(ent.value().starts_with(&alice2.id.to_be_bytes()));
}

#[test]
fn test_insert_with() {
  insert_with(SkipMap::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_insert_with_mmap_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_skipmap_get_or_insert_with_mmap_mut");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  insert_with(SkipMap::mmap_mut(p, open_options, mmap_options).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_insert_with_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE);
  insert_with(SkipMap::mmap_anon(mmap_options).unwrap());
}

fn get_or_remove(l: SkipMap) {
  for i in 0..100 {
    let v = new_value(i);
    l.insert(0, &key(i), &v).unwrap();
  }

  for i in 0..100 {
    let k = key(i);
    let old = l.get_or_remove(0, &k).unwrap().unwrap();
    assert_eq!(old.key(), k);
    assert_eq!(old.value(), new_value(i));
    assert!(!old.is_removed());

    let old = l.get_or_remove(0, &k).unwrap().unwrap();
    assert_eq!(old.key(), k);
    assert_eq!(old.value(), new_value(i));
    assert!(!old.is_removed());
  }

  for i in 0..100 {
    let k = key(i);
    let ent = l.get(0, &k).unwrap();
    assert_eq!(ent.key(), k);
    assert_eq!(ent.value(), new_value(i));
    assert!(!ent.is_removed());
  }
}

#[test]
fn test_get_or_remove() {
  get_or_remove(SkipMap::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_get_or_remove_mmap_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_skipmap_get_or_remove_mmap_mut");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  get_or_remove(SkipMap::mmap_mut(p, open_options, mmap_options).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_get_or_remove_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE);
  get_or_remove(SkipMap::mmap_anon(mmap_options).unwrap());
}

fn remove(l: SkipMap) {
  for i in 0..100 {
    let v = new_value(i);
    l.insert(0, &key(i), &v).unwrap();
  }

  for i in 0..100 {
    let k = key(i);
    let old = l.remove(0, &k).unwrap().unwrap();
    assert_eq!(old.key(), k);
    assert_eq!(old.value(), new_value(i));
    assert!(!old.is_removed());

    let old = l.remove(0, &k).unwrap();
    assert!(old.is_none());
  }

  for i in 0..100 {
    let k = key(i);
    let ent = l.get(0, &k);
    assert!(ent.is_none());
  }
}

#[test]
fn test_remove() {
  remove(SkipMap::new(ARENA_SIZE).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_remove_mmap_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_skipmap_remove_mmap_mut");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  remove(SkipMap::mmap_mut(p, open_options, mmap_options).unwrap());
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_remove_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE);
  remove(SkipMap::mmap_anon(mmap_options).unwrap());
}
