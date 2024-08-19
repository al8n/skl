#![allow(warnings)]

use super::*;
use crate::Descend;

use std::format;

use std::sync::Arc;

use rarena_allocator::Freelist;
#[cfg(feature = "std")]
use wg::WaitGroup;

const ARENA_SIZE: usize = 1 << 20;
#[cfg(feature = "std")]
const BIG_ARENA_SIZE: usize = 120 << 20;
const TEST_OPTIONS: Options = Options::new().with_capacity(ARENA_SIZE as u32);
const UNIFY_TEST_OPTIONS: Options = Options::new()
  .with_capacity(ARENA_SIZE as u32)
  .with_unify(true);
#[cfg(feature = "std")]
const BIG_TEST_OPTIONS: Options = Options::new().with_capacity(BIG_ARENA_SIZE as u32);
#[cfg(feature = "std")]
const UNIFY_BIG_TEST_OPTIONS: Options = Options::new()
  .with_capacity(BIG_ARENA_SIZE as u32)
  .with_unify(true);

fn run(f: impl Fn() + Send + Sync + 'static) {
  f();
}

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

#[test]
fn test_node_ptr_clone() {
  let node_ptr = NodePtr::<u8>::NULL;
  #[allow(clippy::clone_on_copy)]
  let _ = node_ptr.clone();
}

#[test]
fn test_encode_decode_key_size() {
  // Test cases
  let test_cases = [
    (0, 0),                       // Minimum values
    (1, 1),                       // Small values
    (0x1FFFFFF, 0),               // Maximum key_size, minimum height
    (0, 0b11111),                 // Minimum key_size, maximum height
    (0x1FFFFFF, 0b11111),         // Maximum values
    (0x1FFFFFF - 1, 0b11111 - 1), // One less than maximum values
    (12345678, 31),               // Random values
    (0, 1),                       // Edge case: Minimum key_size, small height
    (1, 0),                       // Edge case: Small key_size, minimum height
  ];

  for &(key_size, height) in &test_cases {
    let encoded = encode_key_size_and_height(key_size, height);
    let (decoded_key_size, decoded_height) = decode_key_size_and_height(encoded);

    assert_eq!(key_size, decoded_key_size);
    assert_eq!(height, decoded_height);
  }
}

fn empty_in(l: SkipList) {
  let mut it = l.iter_all_versions(MIN_VERSION);

  assert!(it.seek_lower_bound(Bound::Unbounded).is_none());
  assert!(it.seek_upper_bound(Bound::Unbounded).is_none());
  assert!(it.seek_lower_bound(Bound::Included(b"aaa")).is_none());
  assert!(it.seek_upper_bound(Bound::Excluded(b"aaa")).is_none());
  assert!(it.seek_lower_bound(Bound::Excluded(b"aaa")).is_none());
  assert!(it.seek_upper_bound(Bound::Included(b"aaa")).is_none());
  assert!(l.first(MIN_VERSION).is_none());
  assert!(l.last(MIN_VERSION).is_none());
  assert!(l.ge(MIN_VERSION, b"aaa").is_none());
  assert!(l.lt(MIN_VERSION, b"aaa").is_none());
  assert!(l.gt(MIN_VERSION, b"aaa").is_none());
  assert!(l.le(MIN_VERSION, b"aaa").is_none());
  assert!(l.get(MIN_VERSION, b"aaa").is_none());
  assert!(!l.contains_key(MIN_VERSION, b"aaa"));
  assert!(l.allocated() > 0);
  assert!(l.capacity() > 0);
  assert_eq!(l.remaining(), l.capacity() - l.allocated());
}

#[test]
fn test_empty() {
  run(|| empty_in(SkipList::new().unwrap()));
}

#[test]
fn test_empty_unify() {
  run(|| empty_in(SkipList::with_options(UNIFY_TEST_OPTIONS).unwrap()));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_empty_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_empty_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(1000))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();

    empty_in(SkipList::map_mut(p, open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_empty_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(1000);
    empty_in(SkipList::map_anon(map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_empty_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(1000);
    empty_in(SkipList::map_anon_with_options(TEST_OPTIONS, map_options).unwrap());
  })
}

fn full_in(l: impl FnOnce(usize) -> SkipList) {
  let l = l(1000);
  let mut found_arena_full = false;

  for i in 0..100 {
    if let Err(e) = l.get_or_insert(0u32, &make_int_key(i), &make_value(i), ()) {
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

#[test]
fn test_full() {
  run(|| {
    full_in(|n| {
      SkipList::with_options(
        Options::new()
          .with_capacity(n as u32)
          .with_freelist(Freelist::None),
      )
      .unwrap()
    })
  })
}

#[test]
fn test_full_unify() {
  run(|| {
    full_in(|n| {
      SkipList::with_options(
        UNIFY_TEST_OPTIONS
          .with_capacity(n as u32)
          .with_freelist(Freelist::None),
      )
      .unwrap()
    })
  })
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_full_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_full_map_mut");

    full_in(|n| {
      let open_options = OpenOptions::default()
        .create_new(Some(n as u32))
        .read(true)
        .write(true);
      let map_options = MmapOptions::default();
      SkipList::map_mut_with_options(
        p,
        Options::new().with_freelist(Freelist::None),
        open_options,
        map_options,
      )
      .unwrap()
    });
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_full_map_anon() {
  run(|| {
    full_in(|n| {
      let map_options = MmapOptions::default().len(n as u32);
      SkipList::map_anon_with_options(Options::new().with_freelist(Freelist::None), map_options)
        .unwrap()
    });
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_full_map_anon_unify() {
  run(|| {
    full_in(|n| {
      let map_options = MmapOptions::default().len(n as u32);
      SkipList::map_anon_with_options(Options::new().with_freelist(Freelist::None), map_options)
        .unwrap()
    });
  })
}

fn basic_in(mut l: SkipList) {
  // Try adding values.
  l.get_or_insert(0u8, b"key1", &make_value(1), ()).unwrap();
  l.get_or_insert(0u8, b"key3", &make_value(3), ()).unwrap();
  l.get_or_insert(0u8, b"key2", &make_value(2), ()).unwrap();
  assert_eq!(l.comparator(), &Ascend);

  {
    let mut it = l.iter_all_versions(0u8);
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

  l.get_or_insert(1u8, "a".as_bytes(), &[], ()).unwrap();
  l.get_or_insert(2u8, "a".as_bytes(), &[], ()).unwrap();

  {
    let mut it = l.iter_all_versions(2u8);
    let ent = it.seek_lower_bound(Bound::Included(b"a")).unwrap();
    assert_eq!(ent.key(), b"a");
    assert_eq!(ent.value().unwrap(), &[]);
    assert_eq!(ent.version(), 2);

    let ent = it.next().unwrap();
    assert_eq!(ent.key(), b"a");
    assert_eq!(ent.value().unwrap(), &[]);
    assert_eq!(ent.version(), 1);
  }

  l.get_or_insert(2u8, "b".as_bytes(), &[], ()).unwrap();
  l.get_or_insert(1u8, "b".as_bytes(), &[], ()).unwrap();

  {
    let mut it = l.iter_all_versions(2u8);
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

  l.get_or_insert(2u8, b"b", &[], ()).unwrap().unwrap();

  assert!(l.get_or_insert(2u8, b"c", &[], ()).unwrap().is_none());

  unsafe {
    l.clear().unwrap();
  }

  let l = l.clone();
  {
    let mut it = l.iter_all_versions(0u8);
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
  run(|| basic_in(SkipList::with_options(TEST_OPTIONS).unwrap()))
}

#[test]
fn test_basic_unify() {
  run(|| basic_in(SkipList::with_options(UNIFY_TEST_OPTIONS).unwrap()))
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_basic_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_basic_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    basic_in(SkipList::map_mut(p, open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_basic_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    basic_in(SkipList::map_anon(map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_basic_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    basic_in(SkipList::map_anon_with_options(TEST_OPTIONS, map_options).unwrap());
  })
}

fn iter_all_versions_mvcc(l: SkipList) {
  l.get_or_insert(1u8, b"a", b"a1", ()).unwrap();
  l.get_or_insert(3u8, b"a", b"a2", ()).unwrap();
  l.get_or_insert(1u8, b"c", b"c1", ()).unwrap();
  l.get_or_insert(3u8, b"c", b"c2", ()).unwrap();

  let mut it = l.iter_all_versions(0u8);
  let mut num = 0;
  while it.next().is_some() {
    num += 1;
  }
  assert_eq!(num, 0);

  let mut it = l.iter_all_versions(1u8);
  let mut num = 0;
  while it.next().is_some() {
    num += 1;
  }
  assert_eq!(num, 2);

  let mut it = l.iter_all_versions(2u8);
  let mut num = 0;
  while it.next().is_some() {
    num += 1;
  }
  assert_eq!(num, 2);

  let mut it = l.iter_all_versions(3u8);
  let mut num = 0;
  while it.next().is_some() {
    num += 1;
  }
  assert_eq!(num, 4);

  let mut it = l.iter_all_versions(0u8);
  assert!(it.seek_lower_bound(Bound::Unbounded).is_none());
  assert!(it.seek_upper_bound(Bound::Unbounded).is_none());

  let mut it = l.iter_all_versions(1u8);
  let ent = it.seek_lower_bound(Bound::Unbounded).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value().unwrap(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = it.seek_upper_bound(Bound::Unbounded).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value().unwrap(), b"c1");
  assert_eq!(ent.version(), 1);

  let mut it = l.iter_all_versions(2u8);
  let ent = it.seek_lower_bound(Bound::Unbounded).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value().unwrap(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = it.seek_upper_bound(Bound::Unbounded).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value().unwrap(), b"c1");
  assert_eq!(ent.version(), 1);

  let mut it = l.iter_all_versions(3u8);

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

#[test]
fn test_iter_all_versions_mvcc() {
  run(|| iter_all_versions_mvcc(SkipList::with_options(TEST_OPTIONS).unwrap()));
}

#[test]
fn test_iter_all_versions_mvcc_unify() {
  run(|| iter_all_versions_mvcc(SkipList::with_options(UNIFY_TEST_OPTIONS).unwrap()));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iter_all_versions_mvcc_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir
      .path()
      .join("test_skipmap_iter_all_versions_mvcc_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    iter_all_versions_mvcc(SkipList::map_mut(p, open_options, map_options).unwrap());
  });
}

#[test]
#[cfg(feature = "memmap")]
fn test_iter_all_versions_mvcc_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    iter_all_versions_mvcc(SkipList::map_anon(map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_iter_all_versions_mvcc_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    iter_all_versions_mvcc(
      SkipList::map_anon_with_options(UNIFY_TEST_OPTIONS, map_options).unwrap(),
    );
  })
}

fn ordering() {
  let l = SkipList::with_options_and_comparator(TEST_OPTIONS, Descend).unwrap();

  l.get_or_insert(1u8, b"a1", b"a1", ()).unwrap();
  l.get_or_insert(2u8, b"a2", b"a2", ()).unwrap();
  l.get_or_insert(3u8, b"a3", b"a3", ()).unwrap();

  let mut it = l.iter_all_versions(3u8);
  for i in (1..=3).rev() {
    let ent = it.next().unwrap();
    assert_eq!(ent.key(), format!("a{i}").as_bytes());
    assert_eq!(ent.value().unwrap(), format!("a{i}").as_bytes());
  }
}

#[test]
fn test_ordering() {
  run(ordering);
}

fn get_mvcc(l: SkipList) {
  l.get_or_insert(1u8, b"a", b"a1", ()).unwrap();
  l.get_or_insert(3u8, b"a", b"a2", ()).unwrap();
  l.get_or_insert(1u8, b"c", b"c1", ()).unwrap();
  l.get_or_insert(3u8, b"c", b"c2", ()).unwrap();

  let ent = l.get(1u8, b"a").unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = l.get(2u8, b"a").unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = l.get(3u8, b"a").unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.version(), 3);

  let ent = l.get(4u8, b"a").unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.version(), 3);

  assert!(l.get(0u8, b"b").is_none());
  assert!(l.get(1u8, b"b").is_none());
  assert!(l.get(2u8, b"b").is_none());
  assert!(l.get(3u8, b"b").is_none());
  assert!(l.get(4u8, b"b").is_none());

  let ent = l.get(1u8, b"c").unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.get(2u8, b"c").unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.get(3u8, b"c").unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);

  let ent = l.get(4u8, b"c").unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);

  assert!(l.get(5u8, b"d").is_none());
}

#[test]
fn test_get_mvcc() {
  run(|| get_mvcc(SkipList::with_options(TEST_OPTIONS).unwrap()));
}

#[test]
fn test_get_mvcc_unify() {
  run(|| get_mvcc(SkipList::with_options(UNIFY_TEST_OPTIONS).unwrap()));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_get_mvcc_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_get_mvcc_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    get_mvcc(SkipList::map_mut(p, open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_get_mvcc_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    get_mvcc(SkipList::map_anon(map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_get_mvcc_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    get_mvcc(SkipList::map_anon_with_options(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn gt_in(l: SkipList) {
  l.get_or_insert(1u8, b"a", b"a1", ()).unwrap();
  l.get_or_insert(3u8, b"a", b"a2", ()).unwrap();
  l.get_or_insert(1u8, b"c", b"c1", ()).unwrap();
  l.get_or_insert(3u8, b"c", b"c2", ()).unwrap();
  l.get_or_insert(5u8, b"c", b"c3", ()).unwrap();

  assert!(l.lower_bound(0u8, Bound::Excluded(b"a")).is_none());
  assert!(l.lower_bound(0u8, Bound::Excluded(b"b")).is_none());
  assert!(l.lower_bound(0u8, Bound::Excluded(b"c")).is_none());

  let ent = l.lower_bound(1u8, Bound::Excluded(b"")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(2u8, Bound::Excluded(b"")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(3u8, Bound::Excluded(b"")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(1u8, Bound::Excluded(b"a")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(2u8, Bound::Excluded(b"a")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(3u8, Bound::Excluded(b"a")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(1u8, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(2u8, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(3u8, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(4u8, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(5u8, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c3");
  assert_eq!(ent.version(), 5);

  let ent = l.lower_bound(6u8, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c3");
  assert_eq!(ent.version(), 5);

  assert!(l.lower_bound(1u8, Bound::Excluded(b"c")).is_none());
  assert!(l.lower_bound(2u8, Bound::Excluded(b"c")).is_none());
  assert!(l.lower_bound(3u8, Bound::Excluded(b"c")).is_none());
  assert!(l.lower_bound(4u8, Bound::Excluded(b"c")).is_none());
  assert!(l.lower_bound(5u8, Bound::Excluded(b"c")).is_none());
  assert!(l.lower_bound(6u8, Bound::Excluded(b"c")).is_none());
}

#[test]
fn test_gt() {
  run(|| gt_in(SkipList::with_options(TEST_OPTIONS).unwrap()));
}

#[test]
fn test_gt_unify() {
  run(|| gt_in(SkipList::with_options(UNIFY_TEST_OPTIONS).unwrap()));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_gt_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_gt_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    gt_in(SkipList::map_mut(p, open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_gt_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    gt_in(SkipList::map_anon(map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_gt_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    gt_in(SkipList::map_anon_with_options(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn ge_in(l: SkipList) {
  l.get_or_insert(1u8, b"a", b"a1", ()).unwrap();
  l.get_or_insert(3u8, b"a", b"a2", ()).unwrap();
  l.get_or_insert(1u8, b"c", b"c1", ()).unwrap();
  l.get_or_insert(3u8, b"c", b"c2", ()).unwrap();

  assert!(l.lower_bound(MIN_VERSION, Bound::Included(b"a")).is_none());
  assert!(l.lower_bound(MIN_VERSION, Bound::Included(b"b")).is_none());
  assert!(l.lower_bound(MIN_VERSION, Bound::Included(b"c")).is_none());

  let ent = l.lower_bound(1u8, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(2u8, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(3u8, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(4u8, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(1u8, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(2u8, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(3u8, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(4u8, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(1u8, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(2u8, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.lower_bound(3u8, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);

  let ent = l.lower_bound(4u8, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);

  assert!(l.lower_bound(MIN_VERSION, Bound::Included(b"d")).is_none());
  assert!(l.lower_bound(1u8, Bound::Included(b"d")).is_none());
  assert!(l.lower_bound(2u8, Bound::Included(b"d")).is_none());
  assert!(l.lower_bound(3u8, Bound::Included(b"d")).is_none());
  assert!(l.lower_bound(4u8, Bound::Included(b"d")).is_none());
}

#[test]
fn test_ge() {
  run(|| ge_in(SkipList::with_options(TEST_OPTIONS).unwrap()));
}

#[test]
fn test_ge_unify() {
  run(|| ge_in(SkipList::with_options(UNIFY_TEST_OPTIONS).unwrap()));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_ge_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_ge_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    ge_in(SkipList::map_mut(p, open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_ge_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    ge_in(SkipList::map_anon(map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_ge_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    ge_in(SkipList::map_anon_with_options(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn le_in(l: SkipList) {
  l.get_or_insert(1u8, b"a", b"a1", ()).unwrap();
  l.get_or_insert(3u8, b"a", b"a2", ()).unwrap();
  l.get_or_insert(1u8, b"c", b"c1", ()).unwrap();
  l.get_or_insert(3u8, b"c", b"c2", ()).unwrap();

  assert!(l.upper_bound(MIN_VERSION, Bound::Included(b"a")).is_none());
  assert!(l.upper_bound(MIN_VERSION, Bound::Included(b"b")).is_none());
  assert!(l.upper_bound(MIN_VERSION, Bound::Included(b"c")).is_none());

  let ent = l.upper_bound(1u8, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(2u8, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(3u8, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(4u8, Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(1u8, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(2u8, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(3u8, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(4u8, Bound::Included(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(1u8, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(2u8, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(3u8, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(4u8, Bound::Included(b"c")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(1u8, Bound::Included(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(2u8, Bound::Included(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(3u8, Bound::Included(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(4u8, Bound::Included(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);
}

#[test]
fn test_le() {
  run(|| le_in(SkipList::with_options(TEST_OPTIONS).unwrap()));
}

#[test]
fn test_le_unify() {
  run(|| le_in(SkipList::with_options(UNIFY_TEST_OPTIONS).unwrap()));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_le_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_le_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    gt_in(SkipList::map_mut(p, open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_le_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    gt_in(SkipList::map_anon(map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_le_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    gt_in(SkipList::map_anon_with_options(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn lt_in(l: SkipList) {
  l.get_or_insert(1u8, b"a", b"a1", ()).unwrap();
  l.get_or_insert(3u8, b"a", b"a2", ()).unwrap();
  l.get_or_insert(1u8, b"c", b"c1", ()).unwrap();
  l.get_or_insert(3u8, b"c", b"c2", ()).unwrap();

  assert!(l.upper_bound(MIN_VERSION, Bound::Excluded(b"a")).is_none());
  assert!(l.upper_bound(MIN_VERSION, Bound::Excluded(b"b")).is_none());
  assert!(l.upper_bound(MIN_VERSION, Bound::Excluded(b"c")).is_none());
  assert!(l.upper_bound(1u8, Bound::Excluded(b"a")).is_none());
  assert!(l.upper_bound(2u8, Bound::Excluded(b"a")).is_none());

  let ent = l.upper_bound(1u8, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(2u8, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(3u8, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(4u8, Bound::Excluded(b"b")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(1u8, Bound::Excluded(b"c")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(2u8, Bound::Excluded(b"c")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(3u8, Bound::Excluded(b"c")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(4u8, Bound::Excluded(b"c")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a2");
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(1u8, Bound::Excluded(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(2u8, Bound::Excluded(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c1");
  assert_eq!(ent.version(), 1);

  let ent = l.upper_bound(3u8, Bound::Excluded(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);

  let ent = l.upper_bound(4u8, Bound::Excluded(b"d")).unwrap();
  assert_eq!(ent.key(), b"c");
  assert_eq!(ent.value(), b"c2");
  assert_eq!(ent.version(), 3);
}

#[test]
fn test_lt() {
  run(|| lt_in(SkipList::with_options(TEST_OPTIONS).unwrap()))
}

#[test]
fn test_lt_unify() {
  run(|| lt_in(SkipList::with_options(UNIFY_TEST_OPTIONS).unwrap()))
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_lt_map_mut() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_skipmap_lt_map_mut");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u32))
    .read(true)
    .write(true);
  let map_options = MmapOptions::default();
  lt_in(SkipList::map_mut(p, open_options, map_options).unwrap());
}

#[test]
#[cfg(feature = "memmap")]

fn test_lt_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    lt_in(SkipList::map_anon(map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_lt_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    lt_in(SkipList::map_anon_with_options(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn test_basic_large_testcases_in(l: Arc<SkipList>) {
  let n = 1000;

  for i in 0..n {
    l.get_or_insert(MIN_VERSION, &key(i), &new_value(i), ())
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

#[test]
fn test_basic_large_testcases() {
  run(|| {
    let l = Arc::new(SkipList::with_options(TEST_OPTIONS).unwrap());
    test_basic_large_testcases_in(l);
  })
}

#[test]
fn test_basic_large_testcases_unify() {
  run(|| {
    let l = Arc::new(SkipList::with_options(UNIFY_TEST_OPTIONS).unwrap());
    test_basic_large_testcases_in(l);
  })
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_basic_large_testcases_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir
      .path()
      .join("test_skipmap_basic_large_testcases_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    let l = Arc::new(SkipList::map_mut(p, open_options, map_options).unwrap());
    test_basic_large_testcases_in(l);
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_basic_large_testcases_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    let l = Arc::new(SkipList::map_anon(map_options).unwrap());
    test_basic_large_testcases_in(l);
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_basic_large_testcases_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    let l = Arc::new(SkipList::map_anon_with_options(UNIFY_TEST_OPTIONS, map_options).unwrap());
    test_basic_large_testcases_in(l);
  })
}

#[cfg(feature = "std")]
fn test_concurrent_basic_runner(l: Arc<SkipList>) {
  #[cfg(not(any(miri, feature = "loom")))]
  const N: usize = 1000;
  #[cfg(any(miri, feature = "loom"))]
  const N: usize = 5;

  let wg = Arc::new(());
  for i in 0..N {
    let w = wg.clone();
    let l = l.clone();
    std::thread::spawn(move || {
      l.get_or_insert(MIN_VERSION, &key(i), &new_value(i), ())
        .unwrap();
      drop(w);
    });
  }
  while Arc::strong_count(&wg) > 1 {}
  for i in 0..N {
    let w = wg.clone();
    let l = l.clone();
    std::thread::spawn(move || {
      let k = key(i);
      assert_eq!(
        l.get(MIN_VERSION, &k).unwrap().value(),
        new_value(i),
        "broken: {i}"
      );
      drop(w);
    });
  }
}

#[test]
#[cfg(feature = "std")]
fn test_concurrent_basic() {
  run(|| {
    let l = Arc::new(
      SkipList::with_options(TEST_OPTIONS)
        .unwrap()
        .with_yield_now(),
    );
    test_concurrent_basic_runner(l);
  })
}

#[test]
#[cfg(feature = "std")]
fn test_concurrent_basic_unify() {
  run(|| {
    let l = Arc::new(
      SkipList::with_options(UNIFY_TEST_OPTIONS)
        .unwrap()
        .with_yield_now(),
    );
    test_concurrent_basic_runner(l);
  })
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_concurrent_basic_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_concurrent_basic_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    let l = Arc::new(
      SkipList::map_mut(p, open_options, map_options)
        .unwrap()
        .with_yield_now(),
    );
    test_concurrent_basic_runner(l);
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_concurrent_basic_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    test_concurrent_basic_runner(Arc::new(
      SkipList::map_anon(map_options).unwrap().with_yield_now(),
    ));
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_concurrent_basic_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    test_concurrent_basic_runner(Arc::new(
      SkipList::map_anon_with_options(UNIFY_TEST_OPTIONS, map_options)
        .unwrap()
        .with_yield_now(),
    ));
  })
}

#[cfg(feature = "std")]
fn test_concurrent_basic_2pc_runner(l: Arc<SkipList>) {
  #[cfg(not(any(miri, feature = "loom")))]
  const N: usize = 100;
  #[cfg(any(miri, feature = "loom"))]
  const N: usize = 5;

  let wg = Arc::new(());
  for i in 0..N {
    let w = wg.clone();
    let l = l.clone();
    std::thread::spawn(move || {
      let k = key(i);
      let v = new_value(i);
      let node = l.allocate(MIN_VERSION, &k, &v, ()).unwrap();
      std::thread::sleep(std::time::Duration::from_millis(rand::random::<u8>() as u64));
      l.link(node).unwrap();
      drop(w);
    });
  }
  while Arc::strong_count(&wg) > 1 {}
  for i in 0..N {
    let w = wg.clone();
    let l = l.clone();
    std::thread::spawn(move || {
      let k = key(i);
      assert_eq!(
        l.get(MIN_VERSION, &k).unwrap().value(),
        new_value(i),
        "broken: {i}"
      );
      drop(w);
    });
  }
}

#[test]
#[cfg(feature = "std")]
fn test_concurrent_basic_2pc() {
  run(|| {
    let l = Arc::new(
      SkipList::with_options(TEST_OPTIONS)
        .unwrap()
        .with_yield_now(),
    );
    test_concurrent_basic_2pc_runner(l);
  })
}

#[test]
#[cfg(feature = "std")]
fn test_concurrent_basic_2pc_unify() {
  run(|| {
    let l = Arc::new(
      SkipList::with_options(UNIFY_TEST_OPTIONS)
        .unwrap()
        .with_yield_now(),
    );
    test_concurrent_basic_2pc_runner(l);
  })
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_concurrent_basic_2pc_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_concurrent_basic_2pc_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    let l = Arc::new(
      SkipList::map_mut(p, open_options, map_options)
        .unwrap()
        .with_yield_now(),
    );
    test_concurrent_basic_2pc_runner(l);
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_concurrent_basic_2pc_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    test_concurrent_basic_2pc_runner(Arc::new(
      SkipList::map_anon(map_options).unwrap().with_yield_now(),
    ));
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_concurrent_basic_2pc_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    test_concurrent_basic_2pc_runner(Arc::new(
      SkipList::map_anon_with_options(UNIFY_TEST_OPTIONS, map_options)
        .unwrap()
        .with_yield_now(),
    ));
  })
}

#[cfg(all(feature = "std", not(miri)))]
fn test_concurrent_basic_big_values_runner(l: Arc<SkipList>) {
  #[cfg(not(any(miri, feature = "loom")))]
  const N: usize = 100;
  #[cfg(any(miri, feature = "loom"))]
  const N: usize = 5;

  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      l.get_or_insert(MIN_VERSION, &key(i), &big_value(i), ())
        .unwrap();
    });
  }
  while Arc::strong_count(&l) > 1 {}
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
  while Arc::strong_count(&l) > 1 {}
}

#[test]
#[cfg(all(feature = "std", not(miri)))]
fn test_concurrent_basic_big_values() {
  run(|| {
    test_concurrent_basic_big_values_runner(Arc::new(
      SkipList::with_options(BIG_TEST_OPTIONS)
        .unwrap()
        .with_yield_now(),
    ));
  })
}

#[test]
#[cfg(all(feature = "std", not(miri)))]
fn test_concurrent_basic_big_values_unify() {
  run(|| {
    test_concurrent_basic_big_values_runner(Arc::new(
      SkipList::with_options(UNIFY_BIG_TEST_OPTIONS)
        .unwrap()
        .with_yield_now(),
    ));
  })
}

#[test]
#[cfg(all(feature = "memmap", not(miri)))]
fn test_concurrent_basic_big_values_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir
      .path()
      .join("test_skipmap_concurrent_basic_big_values_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(120 << 20))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    test_concurrent_basic_big_values_runner(Arc::new(
      SkipList::map_mut(p, open_options, map_options)
        .unwrap()
        .with_yield_now(),
    ));
  })
}

#[test]
#[cfg(all(feature = "memmap", not(miri)))]
fn test_concurrent_basic_big_values_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(120 << 20);
    test_concurrent_basic_big_values_runner(Arc::new(
      SkipList::map_anon(map_options).unwrap().with_yield_now(),
    ));
  })
}

#[test]
#[cfg(all(feature = "memmap", not(miri)))]
fn test_concurrent_basic_big_values_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(120 << 20);
    test_concurrent_basic_big_values_runner(Arc::new(
      SkipList::map_anon_with_options(UNIFY_BIG_TEST_OPTIONS, map_options)
        .unwrap()
        .with_yield_now(),
    ));
  })
}

#[cfg(feature = "std")]
fn concurrent_one_key(l: Arc<SkipList>) {
  #[cfg(not(any(miri, feature = "loom")))]
  const N: usize = 100;
  #[cfg(any(miri, feature = "loom"))]
  const N: usize = 5;

  let wg = WaitGroup::new();
  for i in 0..N {
    let wg = wg.add(1);
    let l = l.clone();
    std::thread::spawn(move || {
      let _ = l.get_or_insert(MIN_VERSION, b"thekey", &make_value(i), ());
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
  run(|| {
    concurrent_one_key(Arc::new(
      SkipList::with_options(TEST_OPTIONS)
        .unwrap()
        .with_yield_now(),
    ));
  })
}

#[test]
#[cfg(feature = "std")]
fn test_concurrent_one_key_unify() {
  run(|| {
    concurrent_one_key(Arc::new(
      SkipList::with_options(UNIFY_TEST_OPTIONS)
        .unwrap()
        .with_yield_now(),
    ));
  })
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_concurrent_one_key_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_concurrent_one_key_map_mut");
    let open_options = OpenOptions::default()
      .create(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    concurrent_one_key(Arc::new(
      SkipList::map_mut(p, open_options, map_options)
        .unwrap()
        .with_yield_now(),
    ));
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_concurrent_one_key_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    concurrent_one_key(Arc::new(
      SkipList::map_anon(map_options).unwrap().with_yield_now(),
    ));
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_concurrent_one_key_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    concurrent_one_key(Arc::new(
      SkipList::map_anon_with_options(UNIFY_TEST_OPTIONS, map_options)
        .unwrap()
        .with_yield_now(),
    ));
  })
}

fn iter_all_versions_next(l: SkipList) {
  const N: usize = 100;

  for i in (0..N).rev() {
    l.get_or_insert(MIN_VERSION, &make_int_key(i), &make_value(i), ())
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

#[test]
fn test_iter_all_versions_next() {
  run(|| iter_all_versions_next(SkipList::with_options(TEST_OPTIONS).unwrap()));
}

#[test]
fn test_iter_all_versions_next_unify() {
  run(|| iter_all_versions_next(SkipList::with_options(UNIFY_TEST_OPTIONS).unwrap()));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iter_all_versions_next_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir
      .path()
      .join("test_skipmap_iter_all_versions_next_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    iter_all_versions_next(SkipList::map_mut(p, open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_iter_all_versions_next_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    iter_all_versions_next(SkipList::map_anon(map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_iter_all_versions_next_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    iter_all_versions_next(
      SkipList::map_anon_with_options(UNIFY_TEST_OPTIONS, map_options).unwrap(),
    );
  })
}

fn range_next(l: SkipList) {
  const N: usize = 100;

  for i in (0..N).rev() {
    l.get_or_insert(MIN_VERSION, &make_int_key(i), &make_value(i), ())
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

#[test]
fn test_range_next() {
  run(|| range_next(SkipList::with_options(TEST_OPTIONS).unwrap()));
}

#[test]
fn test_range_next_unify() {
  run(|| range_next(SkipList::with_options(UNIFY_TEST_OPTIONS).unwrap()));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_range_next_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_range_next_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    iter_all_versions_next(SkipList::map_mut(p, open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_range_next_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    iter_all_versions_next(SkipList::map_anon(map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_range_next_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    iter_all_versions_next(
      SkipList::map_anon_with_options(UNIFY_TEST_OPTIONS, map_options).unwrap(),
    );
  })
}

fn iter_all_versions_prev(l: SkipList) {
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(MIN_VERSION, &make_int_key(i), &make_value(i), ())
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

#[test]
fn test_iter_all_versions_next_back() {
  run(|| iter_all_versions_prev(SkipList::with_options(TEST_OPTIONS).unwrap()))
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iter_all_versions_prev_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir
      .path()
      .join("test_skipmap_iter_all_versions_prev_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    iter_all_versions_prev(SkipList::map_mut(p, open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_iter_all_versions_prev_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    iter_all_versions_prev(SkipList::map_anon(map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_iter_all_versions_prev_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    iter_all_versions_prev(
      SkipList::map_anon_with_options(UNIFY_TEST_OPTIONS, map_options).unwrap(),
    );
  })
}

fn range_prev(l: SkipList) {
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(MIN_VERSION, &make_int_key(i), &make_value(i), ())
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

#[test]
fn test_range_prev() {
  run(|| range_prev(SkipList::with_options(TEST_OPTIONS).unwrap()));
}

#[test]
fn test_range_prev_unify() {
  run(|| range_prev(SkipList::with_options(UNIFY_TEST_OPTIONS).unwrap()));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_range_prev_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_range_prev_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    range_prev(SkipList::map_mut(p, open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_range_prev_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    range_prev(SkipList::map_anon(map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_range_prev_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    range_prev(SkipList::map_anon_with_options(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn iter_all_versions_seek_ge(l: SkipList) {
  const N: usize = 100;

  for i in (0..N).rev() {
    let v = i * 10 + 1000;
    l.get_or_insert(MIN_VERSION, &make_int_key(v), &make_value(v), ())
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

  l.get_or_insert(MIN_VERSION, &[], &[], ()).unwrap();
  let ent = it.seek_lower_bound(Bound::Included(b"")).unwrap();
  assert_eq!(ent.key(), &[]);
  assert_eq!(ent.value().unwrap(), &[]);

  let ent = it.seek_lower_bound(Bound::Included(b"")).unwrap();
  assert_eq!(ent.key(), &[]);
  assert_eq!(ent.value().unwrap(), &[]);
}

#[test]
fn test_iter_all_versions_seek_ge() {
  run(|| iter_all_versions_seek_ge(SkipList::with_options(TEST_OPTIONS).unwrap()));
}

#[test]
fn test_iter_all_versions_seek_ge_unify() {
  run(|| iter_all_versions_seek_ge(SkipList::with_options(UNIFY_TEST_OPTIONS).unwrap()));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iter_all_versions_seek_ge_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir
      .path()
      .join("test_skipmap_iter_all_versions_seek_ge_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    iter_all_versions_seek_ge(SkipList::map_mut(p, open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_iter_all_versions_seek_ge_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    iter_all_versions_seek_ge(SkipList::map_anon(map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_iter_all_versions_seek_ge_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    iter_all_versions_seek_ge(
      SkipList::map_anon_with_options(UNIFY_TEST_OPTIONS, map_options).unwrap(),
    );
  })
}

fn iter_all_versions_seek_lt(l: SkipList) {
  const N: usize = 100;

  for i in (0..N).rev() {
    let v = i * 10 + 1000;
    l.get_or_insert(MIN_VERSION, &make_int_key(v), &make_value(v), ())
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

  l.get_or_insert(MIN_VERSION, &[], &[], ()).unwrap();
  assert!(l.lt(MIN_VERSION, &[]).is_none());

  let ent = it.seek_upper_bound(Bound::Excluded(b""));
  assert!(ent.is_none());

  let ent = it.seek_upper_bound(Bound::Excluded(b"\x01")).unwrap();
  assert_eq!(ent.key(), &[]);
  assert_eq!(ent.value().unwrap(), &[]);
}

#[test]
fn test_iter_all_versions_seek_lt() {
  run(|| iter_all_versions_seek_lt(SkipList::with_options(TEST_OPTIONS).unwrap()))
}

#[test]
fn test_iter_all_versions_seek_lt_unify() {
  run(|| iter_all_versions_seek_lt(SkipList::with_options(UNIFY_TEST_OPTIONS).unwrap()))
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iter_all_versions_seek_lt_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir
      .path()
      .join("test_skipmap_iter_all_versions_seek_lt_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    iter_all_versions_seek_lt(SkipList::map_mut(p, open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_iter_all_versions_seek_lt_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    iter_all_versions_seek_lt(SkipList::map_anon(map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_iter_all_versions_seek_lt_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    iter_all_versions_seek_lt(
      SkipList::map_anon_with_options(UNIFY_TEST_OPTIONS, map_options).unwrap(),
    );
  })
}

fn range(l: SkipList) {
  for i in 1..10 {
    l.get_or_insert(MIN_VERSION, &make_int_key(i), &make_value(i), ())
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

#[test]
fn test_range() {
  run(|| range(SkipList::with_options(TEST_OPTIONS).unwrap()))
}

#[test]
fn test_range_unify() {
  run(|| range(SkipList::with_options(UNIFY_TEST_OPTIONS).unwrap()))
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_range_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_range_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    range(SkipList::map_mut(p, open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_range_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    range(SkipList::map_anon(map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_range_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    range(SkipList::map_anon_with_options(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn iter_latest(l: SkipList) {
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(MIN_VERSION, &make_int_key(i), &make_value(i), ())
      .unwrap();
  }

  for i in 50..N {
    l.get_or_insert(1u8, &make_int_key(i), &make_value(i + 1000), ())
      .unwrap();
  }

  for i in 0..50 {
    l.get_or_insert(2u8, &make_int_key(i), &make_value(i + 1000), ())
      .unwrap();
  }

  let mut it = l.iter(4u8);
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
  run(|| iter_latest(SkipList::with_options(TEST_OPTIONS).unwrap()))
}

#[test]
fn test_iter_latest_unify() {
  run(|| iter_latest(SkipList::with_options(UNIFY_TEST_OPTIONS).unwrap()))
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iter_latest_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_iter_latest_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    iter_latest(SkipList::map_mut(p, open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_iter_latest_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    iter_latest(SkipList::map_anon(map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_iter_latest_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    iter_latest(SkipList::map_anon_with_options(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn range_latest(l: SkipList) {
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(MIN_VERSION, &make_int_key(i), &make_value(i), ())
      .unwrap();
  }

  for i in 50..N {
    l.get_or_insert(1u8, &make_int_key(i), &make_value(i + 1000), ())
      .unwrap();
  }

  for i in 0..50 {
    l.get_or_insert(2u8, &make_int_key(i), &make_value(i + 1000), ())
      .unwrap();
  }

  let mut it = l.range::<[u8], _>(4u8, ..);
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
  run(|| range_latest(SkipList::with_options(TEST_OPTIONS).unwrap()))
}

#[test]
fn test_range_latest_unify() {
  run(|| range_latest(SkipList::with_options(UNIFY_TEST_OPTIONS).unwrap()))
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_range_latest_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_range_latest_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    range_latest(SkipList::map_mut(p, open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_range_latest_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    range_latest(SkipList::map_anon(map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_range_latest_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    range_latest(SkipList::map_anon_with_options(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_reopen_mmap() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("reopen_skipmap");
    {
      let open_options = OpenOptions::default()
        .create(Some(ARENA_SIZE as u32))
        .read(true)
        .write(true);
      let map_options = MmapOptions::default();
      let l = SkipList::map_mut(&p, open_options, map_options).unwrap();
      for i in 0..1000 {
        l.get_or_insert(MIN_VERSION, &key(i), &new_value(i), ())
          .unwrap();
      }
      l.flush().unwrap();
    }

    let open_options = OpenOptions::default().read(true);
    let map_options = MmapOptions::default();
    let l = SkipList::<Ascend, u64>::map(&p, open_options, map_options, 0).unwrap();
    assert_eq!(1000, l.len());
    for i in 0..1000 {
      let k = key(i);
      let ent = l.get(MIN_VERSION, &k).unwrap();
      assert_eq!(new_value(i), ent.value());
      assert_eq!(ent.version(), 0);
      assert_eq!(ent.key(), k);
    }
  })
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_reopen_mmap2() {
  run(|| {
    use rand::seq::SliceRandom;

    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("reopen_skipmap2");
    {
      let open_options = OpenOptions::default()
        .create(Some(ARENA_SIZE as u32))
        .read(true)
        .write(true);
      let map_options = MmapOptions::default();
      let l = SkipList::map_mut_with_comparator(&p, open_options, map_options, Ascend).unwrap();
      let mut data = (0..1000).collect::<Vec<usize>>();
      data.shuffle(&mut rand::thread_rng());
      for i in &data {
        let i = *i;
        l.get_or_insert(i as u32, &key(i), &new_value(i), ())
          .unwrap();
      }
      l.flush_async().unwrap();
      assert_eq!(l.max_version(), 999);
      assert_eq!(l.min_version(), 0);

      for i in data {
        let k = key(i);
        let ent = l.get(i as u32, &k).unwrap();
        assert_eq!(new_value(i), ent.value());
        assert_eq!(ent.version(), i as u64);
        assert_eq!(ent.key(), k);
      }
    }

    let open_options = OpenOptions::default().read(true);
    let map_options = MmapOptions::default();
    let l =
      SkipList::<_, ()>::map_with_comparator(&p, open_options, map_options, Ascend, 0).unwrap();
    assert_eq!(1000, l.len());
    let mut data = (0..1000).collect::<Vec<usize>>();
    data.shuffle(&mut rand::thread_rng());
    for i in data {
      let k = key(i);
      let ent = l.get(i as u32, &k).unwrap();
      assert_eq!(new_value(i), ent.value());
      assert_eq!(ent.version(), i as u64);
      assert_eq!(ent.key(), k);
    }
    assert_eq!(l.max_version(), 999);
    assert_eq!(l.min_version(), 0);
  })
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

fn get_or_insert_with_value(l: SkipList) {
  let alice = Person {
    id: 1,
    name: std::string::String::from("Alice"),
  };

  let encoded_size = alice.encoded_size() as u32;

  let vb = ValueBuilder::new(encoded_size, |val| {
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
      "buffer does not have enough space (remaining 0, want 1)"
    );
    Ok(())
  });

  l.get_or_insert_with_value_builder::<()>(1u8, b"alice", vb, ())
    .unwrap();
}

#[test]
fn test_get_or_insert_with_value() {
  run(|| {
    get_or_insert_with_value(SkipList::with_options(TEST_OPTIONS).unwrap());
  })
}

#[test]
fn test_get_or_insert_with_value_unify() {
  run(|| {
    get_or_insert_with_value(SkipList::with_options(UNIFY_TEST_OPTIONS).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_get_or_insert_with_value_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir
      .path()
      .join("test_skipmap_get_or_insert_with_value_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    get_or_insert_with_value(SkipList::map_mut(p, open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_get_or_insert_with_value_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    get_or_insert_with_value(SkipList::map_anon(map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_get_or_insert_with_value_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    get_or_insert_with_value(
      SkipList::map_anon_with_options(UNIFY_TEST_OPTIONS, map_options).unwrap(),
    );
  })
}

fn get_or_insert_with(l: SkipList) {
  let alice = Person {
    id: 1,
    name: std::string::String::from("Alice"),
  };

  let encoded_size = alice.encoded_size() as u32;

  let kb = KeyBuilder::new(5u8.into(), |key: &mut VacantBuffer| {
    key.write(b"alice").unwrap();
    Ok(())
  });

  let vb = ValueBuilder::new(encoded_size, |val: &mut VacantBuffer| {
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
      "buffer does not have enough space (remaining 0, want 1)"
    );
    Ok(())
  });

  l.get_or_insert_with_builders::<()>(1u8, kb, vb, ())
    .unwrap();
}

#[test]
fn test_get_or_insert_with() {
  run(|| get_or_insert_with(SkipList::with_options(TEST_OPTIONS).unwrap()))
}

#[test]
fn test_get_or_insert_with_unify() {
  run(|| get_or_insert_with(SkipList::with_options(UNIFY_TEST_OPTIONS).unwrap()))
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_get_or_insert_with_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_get_or_insert_with_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    get_or_insert_with(SkipList::map_mut(p, open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_get_or_insert_with_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    get_or_insert_with(SkipList::map_anon(map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_get_or_insert_with_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    get_or_insert_with(SkipList::map_anon_with_options(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn insert_in(l: SkipList) {
  let k = 0u64.to_le_bytes();
  for i in 0..100 {
    let v = new_value(i);
    let old = l.insert(MIN_VERSION, &k, &v, ()).unwrap();
    if let Some(old) = old {
      assert_eq!(old.key(), k);
      assert_eq!(old.value(), new_value(i - 1));
    }
  }

  let ent = l.get(MIN_VERSION, &k).unwrap();
  assert_eq!(ent.key(), k);
  assert_eq!(ent.value(), new_value(99));
}

#[test]
fn test_insert_in() {
  run(|| {
    insert_in(SkipList::with_options(TEST_OPTIONS).unwrap());
  })
}

#[test]
fn test_insert_in_unify() {
  run(|| {
    insert_in(SkipList::with_options(UNIFY_TEST_OPTIONS).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_insert_in_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_insert_in_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    insert_in(SkipList::map_mut(p, open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_insert_in_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    insert_in(SkipList::map_anon(map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_insert_in_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    insert_in(SkipList::map_anon_with_options(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn insert_with_value(l: SkipList) {
  let alice = Person {
    id: 1,
    name: std::string::String::from("Alice"),
  };

  let encoded_size = alice.encoded_size() as u32;

  let vb = ValueBuilder::new(encoded_size, |val| {
    assert_eq!(val.capacity(), encoded_size as usize);
    assert!(val.is_empty());
    val.write(&alice.id.to_le_bytes()).unwrap();
    assert_eq!(val.len(), 4);
    assert_eq!(val.remaining(), encoded_size as usize - 4);
    assert_eq!(val, alice.id.to_le_bytes());
    val[..4].copy_from_slice(&alice.id.to_be_bytes());
    assert_eq!(val, alice.id.to_be_bytes());
    val.write(alice.name.as_bytes()).unwrap();
    assert_eq!(val.len(), encoded_size as usize);
    let err = val.write(&[1]).unwrap_err();
    assert_eq!(
      std::string::ToString::to_string(&err),
      "buffer does not have enough space (remaining 0, want 1)"
    );
    Ok(())
  });

  l.insert_with_value_builder::<()>(1u8, b"alice", vb, ())
    .unwrap();

  let alice2 = Person {
    id: 2,
    name: std::string::String::from("Alice"),
  };

  let vb = ValueBuilder::new(encoded_size, |val| {
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
      "buffer does not have enough space (remaining 0, want 1)"
    );
    Ok(())
  });

  let old = l
    .insert_with_value_builder::<()>(1u8, b"alice", vb, ())
    .unwrap()
    .unwrap();

  assert_eq!(old.key(), b"alice");
  assert!(old.value().starts_with(&alice.id.to_be_bytes()));

  let ent = l.get(1u8, b"alice").unwrap();
  assert_eq!(ent.key(), b"alice");
  assert!(ent.value().starts_with(&alice2.id.to_be_bytes()));
}

#[test]
fn test_insert_with_value() {
  run(|| insert_with_value(SkipList::with_options(TEST_OPTIONS).unwrap()));
}

#[test]
fn test_insert_with_value_unify() {
  run(|| insert_with_value(SkipList::with_options(UNIFY_TEST_OPTIONS).unwrap()));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_insert_with_value_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir
      .path()
      .join("test_skipmap_get_or_insert_with_value_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    insert_with_value(SkipList::map_mut(p, open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_insert_with_value_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    insert_with_value(SkipList::map_anon(map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_insert_with_value_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    insert_with_value(SkipList::map_anon_with_options(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn insert_with(l: SkipList) {
  let alice = Person {
    id: 1,
    name: std::string::String::from("Alice"),
  };

  let encoded_size = alice.encoded_size() as u32;

  let kb = KeyBuilder::new(5u8.into(), |key: &mut VacantBuffer| {
    key.write(b"alice").unwrap();
    Ok(())
  });

  let vb = ValueBuilder::new(encoded_size as u32, |val: &mut VacantBuffer| {
    assert_eq!(val.capacity(), encoded_size as usize);
    assert!(val.is_empty());
    val.write(&alice.id.to_le_bytes()).unwrap();
    assert_eq!(val.len(), 4);
    assert_eq!(val.remaining(), encoded_size as usize - 4);
    assert_eq!(val, alice.id.to_le_bytes());
    val[..4].copy_from_slice(&alice.id.to_be_bytes());
    assert_eq!(val, alice.id.to_be_bytes());
    val.write(alice.name.as_bytes()).unwrap();
    assert_eq!(val.len(), encoded_size as usize);
    let err = val.write(&[1]).unwrap_err();
    assert_eq!(
      std::string::ToString::to_string(&err),
      "buffer does not have enough space (remaining 0, want 1)"
    );
    Ok(())
  });

  l.insert_with_builders::<()>(1u8, kb, vb, ()).unwrap();

  let alice2 = Person {
    id: 2,
    name: std::string::String::from("Alice"),
  };

  let vb = ValueBuilder::new(encoded_size, |val: &mut VacantBuffer| {
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
      "buffer does not have enough space (remaining 0, want 1)"
    );
    Ok(())
  });
  let old = l
    .insert_with_builders::<()>(1u8, kb, vb, ())
    .unwrap()
    .unwrap();

  assert_eq!(old.key(), b"alice");
  assert!(old.value().starts_with(&alice.id.to_be_bytes()));

  let ent = l.get(1u8, b"alice").unwrap();
  assert_eq!(ent.key(), b"alice");
  assert!(ent.value().starts_with(&alice2.id.to_be_bytes()));
}

#[test]
fn test_insert_with() {
  run(|| insert_with(SkipList::with_options(TEST_OPTIONS).unwrap()))
}

#[test]
fn test_insert_with_unify() {
  run(|| insert_with(SkipList::with_options(UNIFY_TEST_OPTIONS).unwrap()))
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_insert_with_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_insert_with_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    insert_with(SkipList::map_mut(p, open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_insert_with_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    insert_with(SkipList::map_anon(map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_insert_with_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    insert_with(SkipList::map_anon_with_options(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn get_or_remove(l: SkipList) {
  for i in 0..100 {
    let v = new_value(i);
    l.insert(MIN_VERSION, &key(i), &v, ()).unwrap();
  }

  for i in 0..100 {
    let k = key(i);
    let old = l.get_or_remove(MIN_VERSION, &k, ()).unwrap().unwrap();
    assert_eq!(old.key(), k);
    assert_eq!(old.value(), new_value(i));

    let old = l.get_or_remove(MIN_VERSION, &k, ()).unwrap().unwrap();
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

#[test]
fn test_get_or_remove() {
  run(|| get_or_remove(SkipList::with_options(TEST_OPTIONS).unwrap()))
}

#[test]
fn test_get_or_remove_unify() {
  run(|| get_or_remove(SkipList::with_options(UNIFY_TEST_OPTIONS).unwrap()))
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_get_or_remove_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_get_or_remove_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    get_or_remove(SkipList::map_mut(p, open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_get_or_remove_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    get_or_remove(SkipList::map_anon(map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_get_or_remove_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    get_or_remove(SkipList::map_anon_with_options(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn remove(l: SkipList) {
  for i in 0..100 {
    let v = new_value(i);
    l.insert(MIN_VERSION, &key(i), &v, ()).unwrap();
  }

  for i in 0..100 {
    let k = key(i);
    // no race, remove should succeed
    let old = l
      .compare_remove(MIN_VERSION, &k, (), Ordering::SeqCst, Ordering::Acquire)
      .unwrap();
    assert!(old.is_none());

    // key already removed
    let old = l
      .compare_remove(MIN_VERSION, &k, (), Ordering::SeqCst, Ordering::Acquire)
      .unwrap();
    assert!(old.is_none());
  }

  for i in 0..100 {
    let k = key(i);
    let ent = l.get(MIN_VERSION, &k);
    assert!(ent.is_none());
  }
}

#[test]
fn test_remove() {
  run(|| remove(SkipList::with_options(TEST_OPTIONS).unwrap()))
}

#[test]
fn test_remove_unify() {
  run(|| remove(SkipList::with_options(UNIFY_TEST_OPTIONS).unwrap()))
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_remove_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_remove_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    remove(SkipList::map_mut(p, open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_remove_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    remove(SkipList::map_anon(map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_remove_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    remove(SkipList::map_anon_with_options(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn remove2(l: SkipList) {
  for i in 0..100 {
    let v = new_value(i);
    l.insert(MIN_VERSION, &key(i), &v, ()).unwrap();
  }

  for i in 0..100 {
    let k = key(i);
    // not found, remove should succeed
    let old = l
      .compare_remove(1u8, &k, (), Ordering::SeqCst, Ordering::Acquire)
      .unwrap();
    assert!(old.is_none());

    // no-race, remove should succeed
    let old = l
      .compare_remove(MIN_VERSION, &k, (), Ordering::SeqCst, Ordering::Acquire)
      .unwrap();
    assert!(old.is_none());
  }

  for i in 0..100 {
    let k = key(i);
    let ent = l.get(MIN_VERSION, &k);
    assert!(ent.is_none());
  }
}

#[test]
fn test_remove2() {
  run(|| remove2(SkipList::with_options(TEST_OPTIONS).unwrap()))
}

#[test]
fn test_remove2_unify() {
  run(|| remove2(SkipList::with_options(UNIFY_TEST_OPTIONS).unwrap()))
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_remove2_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_remove2_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    remove2(SkipList::map_mut(p, open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_remove2_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    remove2(SkipList::map_anon(map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_remove2_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    remove2(SkipList::map_anon_with_options(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn allocate_in(map: SkipList) {
  let unlinked_node = map.allocate(MIN_VERSION, b"hello", b"world", ()).unwrap();
  map.link(unlinked_node).unwrap();

  let entry = map.get(MIN_VERSION, b"hello").unwrap();
  assert_eq!(entry.value(), b"world");

  let unlinked_node2 = map.allocate(MIN_VERSION, b"hello", b"rust", ()).unwrap();
  map.link(unlinked_node2).unwrap();

  let entry = map.get(MIN_VERSION, b"hello").unwrap();
  assert_eq!(entry.value(), b"rust");
}

#[test]
fn test_allocate_in() {
  run(|| allocate_in(SkipList::with_options(TEST_OPTIONS).unwrap()))
}

#[test]
fn test_allocate_in_unify() {
  run(|| allocate_in(SkipList::with_options(UNIFY_TEST_OPTIONS).unwrap()))
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_allocate_in_map_mut() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_allocate_in_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    allocate_in(SkipList::map_mut(p, open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_allocate_in_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    allocate_in(SkipList::map_anon(map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_allocate_in_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    allocate_in(SkipList::map_anon_with_options(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

#[test]
fn test_estimited_size() {
  let l = SkipList::new().unwrap();

  let h = l.random_height();
  let size = SkipList::<u64>::estimated_node_size(h, 3usize, 3);
  let allocated = l.allocated();
  l.allocate_at_height(1u8, h, b"key", b"val", ());
  let allocated2 = l.allocated();
  let actual = allocated2 - allocated;
  assert!(size - 7 - (mem::align_of::<u64>() - 1) < actual && actual < size);
}
