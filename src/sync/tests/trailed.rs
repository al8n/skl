use super::*;

type SkipList<T, C> = crate::sync::trailed::SkipMap<T, C>;

type SkipMap = crate::sync::trailed::SkipMap<u64, Ascend>;

fn trailer() -> u64 {
  123456789
}

fn empty_in(l: SkipMap) {
  let mut it = l.iter();

  assert!(it.seek_lower_bound(Bound::Unbounded).is_none());
  assert!(it.seek_upper_bound(Bound::Unbounded).is_none());
  assert!(it.seek_lower_bound(Bound::Included(b"aaa")).is_none());
  assert!(it.seek_upper_bound(Bound::Excluded(b"aaa")).is_none());
  assert!(it.seek_lower_bound(Bound::Excluded(b"aaa")).is_none());
  assert!(it.seek_upper_bound(Bound::Included(b"aaa")).is_none());
  assert!(l.first().is_none());
  assert!(l.last().is_none());
  assert!(l.get(b"aaa").is_none());
  assert!(!l.contains_key(b"aaa"));
  assert!(l.allocated() > 0);
  assert!(l.capacity() > 0);
  assert_eq!(l.remaining(), l.capacity() - l.allocated());
}

#[test]
fn test_empty() {
  run(|| empty_in(SkipList::new(Options::new()).unwrap()));
}

#[test]
fn test_empty_unify() {
  run(|| empty_in(SkipList::new(UNIFY_TEST_OPTIONS).unwrap()));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_empty_map_mut() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_empty_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(1000))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();

    let x = SkipList::map_mut(p, Options::new(), open_options, map_options).unwrap();
    empty_in(x);
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_empty_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(1000);
    empty_in(SkipList::map_anon(Options::new(), map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_empty_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(1000);
    empty_in(SkipList::map_anon(TEST_OPTIONS, map_options).unwrap());
  })
}

fn full_in(l: impl FnOnce(usize) -> SkipMap) {
  let l = l(1000);
  let mut found_arena_full = false;

  for i in 0..100 {
    if let Err(e) = l.get_or_insert(&make_int_key(i), &make_value(i), trailer()) {
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
      SkipList::new(
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
      SkipList::new(
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
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_full_map_mut");

    full_in(|n| {
      let open_options = OpenOptions::default()
        .create_new(Some(n as u32))
        .read(true)
        .write(true);
      let map_options = MmapOptions::default();
      SkipList::map_mut(
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
      SkipList::map_anon(Options::new().with_freelist(Freelist::None), map_options).unwrap()
    });
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_full_map_anon_unify() {
  run(|| {
    full_in(|n| {
      let map_options = MmapOptions::default().len(n as u32);
      SkipList::map_anon(Options::new().with_freelist(Freelist::None), map_options).unwrap()
    });
  })
}

fn basic_in(mut l: SkipMap) {
  // Try adding values.
  l.get_or_insert(b"key1", &make_value(1), trailer()).unwrap();
  l.get_or_insert(b"key3", &make_value(3), trailer()).unwrap();
  l.get_or_insert(b"key2", &make_value(2), trailer()).unwrap();
  assert_eq!(l.comparator(), &Ascend);

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

  l.get_or_insert("a".as_bytes(), &[], trailer()).unwrap();
  l.get_or_insert("a".as_bytes(), &[], trailer()).unwrap();

  {
    let mut it = l.iter();
    let ent = it.seek_lower_bound(Bound::Included(b"a")).unwrap();
    assert_eq!(ent.key(), b"a");
    assert_eq!(ent.value(), &[]);

    let ent = it.next().unwrap();
    assert_eq!(ent.key(), b"key1");
    assert_eq!(ent.value(), &make_value(1));
  }

  l.get_or_insert("b".as_bytes(), &[], trailer()).unwrap();
  l.get_or_insert("b".as_bytes(), &[], trailer()).unwrap();

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

  l.get_or_insert(b"b", &[], trailer()).unwrap().unwrap();

  assert!(l.get_or_insert(b"c", &[], trailer()).unwrap().is_none());

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

#[test]
fn test_basic() {
  run(|| basic_in(SkipList::new(TEST_OPTIONS).unwrap()))
}

#[test]
fn test_basic_unify() {
  run(|| basic_in(SkipList::new(UNIFY_TEST_OPTIONS).unwrap()))
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_basic_map_mut() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_basic_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    basic_in(SkipList::map_mut(p, Options::new(), open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_basic_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    basic_in(SkipList::map_anon(Options::new(), map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_basic_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    basic_in(SkipList::map_anon(TEST_OPTIONS, map_options).unwrap());
  })
}

fn ordering() {
  let l = SkipList::with_comparator(TEST_OPTIONS, Descend).unwrap();

  l.get_or_insert(b"a1", b"a1", trailer()).unwrap();
  l.get_or_insert(b"a2", b"a2", trailer()).unwrap();
  l.get_or_insert(b"a3", b"a3", trailer()).unwrap();

  let mut it = l.iter();
  for i in (1..=3).rev() {
    let ent = it.next().unwrap();
    assert_eq!(ent.key(), format!("a{i}").as_bytes());
    assert_eq!(ent.value(), format!("a{i}").as_bytes());
  }
}

#[test]
fn test_ordering() {
  run(ordering);
}

fn get(l: SkipMap) {
  l.get_or_insert(b"a", b"a1", trailer()).unwrap();
  l.get_or_insert(b"a", b"a2", trailer()).unwrap();
  l.get_or_insert(b"c", b"c1", trailer()).unwrap();
  l.get_or_insert(b"c", b"c2", trailer()).unwrap();

  let ent = l.get(b"a").unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");

  let ent = l.get(b"a").unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");

  let ent = l.get(b"a").unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");

  l.insert(b"a", b"a2", trailer()).unwrap();

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

#[test]
fn test_get() {
  run(|| get(SkipList::new(TEST_OPTIONS).unwrap()));
}

#[test]
fn test_get_unify() {
  run(|| get(SkipList::new(UNIFY_TEST_OPTIONS).unwrap()));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_get_map_mut() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_get_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    get(SkipList::map_mut(p, Options::new(), open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_get_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    get(SkipList::map_anon(Options::new(), map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_get_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    get(SkipList::map_anon(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn gt_in(l: SkipMap) {
  l.get_or_insert(b"a", b"a1", trailer()).unwrap();
  l.get_or_insert(b"a", b"a2", trailer()).unwrap();
  l.get_or_insert(b"c", b"c1", trailer()).unwrap();
  l.get_or_insert(b"c", b"c2", trailer()).unwrap();
  l.get_or_insert(b"c", b"c3", trailer()).unwrap();

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

#[test]
fn test_gt() {
  run(|| gt_in(SkipList::new(TEST_OPTIONS).unwrap()));
}

#[test]
fn test_gt_unify() {
  run(|| gt_in(SkipList::new(UNIFY_TEST_OPTIONS).unwrap()));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_gt_map_mut() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_gt_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    gt_in(SkipList::map_mut(p, Options::new(), open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_gt_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    gt_in(SkipList::map_anon(Options::new(), map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_gt_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    gt_in(SkipList::map_anon(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn ge_in(l: SkipMap) {
  l.get_or_insert(b"a", b"a1", trailer()).unwrap();
  l.get_or_insert(b"a", b"a2", trailer()).unwrap();
  l.get_or_insert(b"c", b"c1", trailer()).unwrap();
  l.get_or_insert(b"c", b"c2", trailer()).unwrap();

  assert!(l.lower_bound(Bound::Included(b"a")).is_some());
  assert!(l.lower_bound(Bound::Included(b"b")).is_some());
  assert!(l.lower_bound(Bound::Included(b"c")).is_some());

  let ent = l.lower_bound(Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");

  let ent = l.lower_bound(Bound::Included(b"a")).unwrap();
  assert_eq!(ent.key(), b"a");
  assert_eq!(ent.value(), b"a1");

  l.insert(b"a", b"a2", trailer()).unwrap();

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

#[test]
fn test_ge() {
  run(|| ge_in(SkipList::new(TEST_OPTIONS).unwrap()));
}

#[test]
fn test_ge_unify() {
  run(|| ge_in(SkipList::new(UNIFY_TEST_OPTIONS).unwrap()));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_ge_map_mut() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_ge_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    ge_in(SkipList::map_mut(p, Options::new(), open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_ge_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    ge_in(SkipList::map_anon(Options::new(), map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_ge_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    ge_in(SkipList::map_anon(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn le_in(l: SkipMap) {
  l.get_or_insert(b"a", b"a1", trailer()).unwrap();
  l.get_or_insert(b"a", b"a2", trailer()).unwrap();
  l.get_or_insert(b"c", b"c1", trailer()).unwrap();
  l.get_or_insert(b"c", b"c2", trailer()).unwrap();

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

#[test]
fn test_le() {
  run(|| le_in(SkipList::new(TEST_OPTIONS).unwrap()));
}

#[test]
fn test_le_unify() {
  run(|| le_in(SkipList::new(UNIFY_TEST_OPTIONS).unwrap()));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_le_map_mut() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_le_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    gt_in(SkipList::map_mut(p, Options::new(), open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_le_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    gt_in(SkipList::map_anon(Options::new(), map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_le_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    gt_in(SkipList::map_anon(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn lt_in(l: SkipMap) {
  l.get_or_insert(b"a", b"a1", trailer()).unwrap();
  l.get_or_insert(b"a", b"a2", trailer()).unwrap();
  l.get_or_insert(b"c", b"c1", trailer()).unwrap();
  l.get_or_insert(b"c", b"c2", trailer()).unwrap();

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

#[test]
fn test_lt() {
  run(|| lt_in(SkipList::new(TEST_OPTIONS).unwrap()))
}

#[test]
fn test_lt_unify() {
  run(|| lt_in(SkipList::new(UNIFY_TEST_OPTIONS).unwrap()))
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
  lt_in(unsafe { SkipList::map_mut(p, Options::new(), open_options, map_options).unwrap() });
}

#[test]
#[cfg(feature = "memmap")]

fn test_lt_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    lt_in(SkipList::map_anon(Options::new(), map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_lt_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    lt_in(SkipList::map_anon(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn test_basic_large_testcases_in(l: SkipMap) {
  let n = 1000;

  for i in 0..n {
    l.get_or_insert(&key(i), &new_value(i), trailer()).unwrap();
  }

  for i in 0..n {
    let k = key(i);
    let ent = l.get(&k).unwrap();
    assert_eq!(new_value(i), ent.value());

    assert_eq!(ent.key(), k);
  }

  assert_eq!(n, l.len());
}

#[test]
fn test_basic_large_testcases() {
  run(|| {
    let l = SkipList::new(TEST_OPTIONS).unwrap();
    test_basic_large_testcases_in(l);
  })
}

#[test]
fn test_basic_large_testcases_unify() {
  run(|| {
    let l = SkipList::new(UNIFY_TEST_OPTIONS).unwrap();
    test_basic_large_testcases_in(l);
  })
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_basic_large_testcases_map_mut() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir
      .path()
      .join("test_skipmap_basic_large_testcases_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    let l = SkipList::map_mut(p, Options::new(), open_options, map_options).unwrap();
    test_basic_large_testcases_in(l);
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_basic_large_testcases_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    let l = SkipList::map_anon(Options::new(), map_options).unwrap();
    test_basic_large_testcases_in(l);
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_basic_large_testcases_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    let l = SkipList::map_anon(UNIFY_TEST_OPTIONS, map_options).unwrap();
    test_basic_large_testcases_in(l);
  })
}

#[cfg(feature = "std")]
fn test_concurrent_basic_runner(l: SkipMap) {
  #[cfg(not(any(miri, feature = "loom")))]
  const N: usize = 1000;
  #[cfg(any(miri, feature = "loom"))]
  const N: usize = 5;

  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      l.get_or_insert(&key(i), &new_value(i), trailer()).unwrap();
    });
  }
  while l.refs() > 1 {}
  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      let k = key(i);
      assert_eq!(l.get(&k).unwrap().value(), new_value(i), "broken: {i}");
    });
  }
}

#[test]
#[cfg(feature = "std")]
fn test_concurrent_basic() {
  run(|| {
    let l = SkipList::new(TEST_OPTIONS).unwrap().with_yield_now();
    test_concurrent_basic_runner(l);
  })
}

#[test]
#[cfg(feature = "std")]
fn test_concurrent_basic_unify() {
  run(|| {
    let l = SkipList::new(UNIFY_TEST_OPTIONS).unwrap().with_yield_now();
    test_concurrent_basic_runner(l);
  })
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_concurrent_basic_map_mut() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_concurrent_basic_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    let l = SkipList::map_mut(p, Options::new(), open_options, map_options)
      .unwrap()
      .with_yield_now();
    test_concurrent_basic_runner(l);
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_concurrent_basic_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    test_concurrent_basic_runner(
      SkipList::map_anon(Options::new(), map_options)
        .unwrap()
        .with_yield_now(),
    );
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_concurrent_basic_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    test_concurrent_basic_runner(
      SkipList::map_anon(UNIFY_TEST_OPTIONS, map_options)
        .unwrap()
        .with_yield_now(),
    );
  })
}

#[cfg(all(feature = "std", not(miri)))]
fn test_concurrent_basic_big_values_runner(l: SkipMap) {
  #[cfg(not(any(miri, feature = "loom")))]
  const N: usize = 100;
  #[cfg(any(miri, feature = "loom"))]
  const N: usize = 5;

  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      l.get_or_insert(&key(i), &big_value(i), trailer()).unwrap();
    });
  }
  while l.refs() > 1 {}
  // assert_eq!(N, l.len());
  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      let k = key(i);
      assert_eq!(l.get(&k).unwrap().value(), big_value(i), "broken: {i}");
    });
  }
  while l.refs() > 1 {}
}

#[test]
#[cfg(all(feature = "std", not(miri)))]
fn test_concurrent_basic_big_values() {
  run(|| {
    test_concurrent_basic_big_values_runner(
      SkipList::new(BIG_TEST_OPTIONS).unwrap().with_yield_now(),
    );
  })
}

#[test]
#[cfg(all(feature = "std", not(miri)))]
fn test_concurrent_basic_big_values_unify() {
  run(|| {
    test_concurrent_basic_big_values_runner(
      SkipList::new(UNIFY_BIG_TEST_OPTIONS)
        .unwrap()
        .with_yield_now(),
    );
  })
}

#[test]
#[cfg(all(feature = "memmap", not(miri)))]
fn test_concurrent_basic_big_values_map_mut() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir
      .path()
      .join("test_skipmap_concurrent_basic_big_values_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(120 << 20))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    test_concurrent_basic_big_values_runner(
      SkipList::map_mut(p, Options::new(), open_options, map_options)
        .unwrap()
        .with_yield_now(),
    );
  })
}

#[test]
#[cfg(all(feature = "memmap", not(miri)))]
fn test_concurrent_basic_big_values_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(120 << 20);
    test_concurrent_basic_big_values_runner(
      SkipList::map_anon(Options::new(), map_options)
        .unwrap()
        .with_yield_now(),
    );
  })
}

#[test]
#[cfg(all(feature = "memmap", not(miri)))]
fn test_concurrent_basic_big_values_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(120 << 20);
    test_concurrent_basic_big_values_runner(
      SkipList::map_anon(UNIFY_BIG_TEST_OPTIONS, map_options)
        .unwrap()
        .with_yield_now(),
    );
  })
}

#[cfg(feature = "std")]
fn concurrent_one_key(l: SkipMap) {
  #[cfg(not(any(miri, feature = "loom")))]
  const N: usize = 5;
  #[cfg(any(miri, feature = "loom"))]
  const N: usize = 5;

  let wg = WaitGroup::new();
  for i in 0..N {
    let wg = wg.add(1);
    let l = l.clone();
    std::thread::spawn(move || {
      let _ = l.get_or_insert(b"thekey", &make_value(i), trailer());
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
    concurrent_one_key(SkipList::new(TEST_OPTIONS).unwrap().with_yield_now());
  })
}

#[test]
#[cfg(feature = "std")]
fn test_concurrent_one_key_unify() {
  run(|| {
    concurrent_one_key(SkipList::new(UNIFY_TEST_OPTIONS).unwrap().with_yield_now());
  })
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_concurrent_one_key_map_mut() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_concurrent_one_key_map_mut");
    let open_options = OpenOptions::default()
      .create(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    concurrent_one_key(
      SkipList::map_mut(p, Options::new(), open_options, map_options)
        .unwrap()
        .with_yield_now(),
    );
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_concurrent_one_key_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    concurrent_one_key(
      SkipList::map_anon(Options::new(), map_options)
        .unwrap()
        .with_yield_now(),
    );
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_concurrent_one_key_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    concurrent_one_key(
      SkipList::map_anon(UNIFY_TEST_OPTIONS, map_options)
        .unwrap()
        .with_yield_now(),
    );
  })
}

fn iter_all_versions_next(l: SkipMap) {
  const N: usize = 100;

  for i in (0..N).rev() {
    l.get_or_insert(&make_int_key(i), &make_value(i), trailer())
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

#[test]
fn test_iter_all_versions_next() {
  run(|| iter_all_versions_next(SkipList::new(TEST_OPTIONS).unwrap()));
}

#[test]
fn test_iter_all_versions_next_unify() {
  run(|| iter_all_versions_next(SkipList::new(UNIFY_TEST_OPTIONS).unwrap()));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iter_all_versions_next_map_mut() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir
      .path()
      .join("test_skipmap_iter_all_versions_next_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    iter_all_versions_next(
      SkipList::map_mut(p, Options::new(), open_options, map_options).unwrap(),
    );
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_iter_all_versions_next_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    iter_all_versions_next(SkipList::map_anon(Options::new(), map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_iter_all_versions_next_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    iter_all_versions_next(SkipList::map_anon(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn range_next(l: SkipMap) {
  const N: usize = 100;

  for i in (0..N).rev() {
    l.get_or_insert(&make_int_key(i), &make_value(i), trailer())
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

#[test]
fn test_range_next() {
  run(|| range_next(SkipList::new(TEST_OPTIONS).unwrap()));
}

#[test]
fn test_range_next_unify() {
  run(|| range_next(SkipList::new(UNIFY_TEST_OPTIONS).unwrap()));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_range_next_map_mut() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_range_next_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    iter_all_versions_next(
      SkipList::map_mut(p, Options::new(), open_options, map_options).unwrap(),
    );
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_range_next_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    iter_all_versions_next(SkipList::map_anon(Options::new(), map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_range_next_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    iter_all_versions_next(SkipList::map_anon(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn iter_all_versions_prev(l: SkipMap) {
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(&make_int_key(i), &make_value(i), trailer())
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

#[test]
fn test_iter_all_versions_next_back() {
  run(|| iter_all_versions_prev(SkipList::new(TEST_OPTIONS).unwrap()))
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iter_all_versions_prev_map_mut() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir
      .path()
      .join("test_skipmap_iter_all_versions_prev_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    iter_all_versions_prev(
      SkipList::map_mut(p, Options::new(), open_options, map_options).unwrap(),
    );
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_iter_all_versions_prev_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    iter_all_versions_prev(SkipList::map_anon(Options::new(), map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_iter_all_versions_prev_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    iter_all_versions_prev(SkipList::map_anon(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn range_prev(l: SkipMap) {
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(&make_int_key(i), &make_value(i), trailer())
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

#[test]
fn test_range_prev() {
  run(|| range_prev(SkipList::new(TEST_OPTIONS).unwrap()));
}

#[test]
fn test_range_prev_unify() {
  run(|| range_prev(SkipList::new(UNIFY_TEST_OPTIONS).unwrap()));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_range_prev_map_mut() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_range_prev_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    range_prev(SkipList::map_mut(p, Options::new(), open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_range_prev_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    range_prev(SkipList::map_anon(Options::new(), map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_range_prev_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    range_prev(SkipList::map_anon(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn iter_all_versions_seek_ge(l: SkipMap) {
  const N: usize = 100;

  for i in (0..N).rev() {
    let v = i * 10 + 1000;
    l.get_or_insert(&make_int_key(v), &make_value(v), trailer())
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

  l.get_or_insert(&[], &[], trailer()).unwrap();
  let ent = it.seek_lower_bound(Bound::Included(b"")).unwrap();
  assert_eq!(ent.key(), &[]);
  assert_eq!(ent.value(), &[]);

  let ent = it.seek_lower_bound(Bound::Included(b"")).unwrap();
  assert_eq!(ent.key(), &[]);
  assert_eq!(ent.value(), &[]);
}

#[test]
fn test_iter_all_versions_seek_ge() {
  run(|| iter_all_versions_seek_ge(SkipList::new(TEST_OPTIONS).unwrap()));
}

#[test]
fn test_iter_all_versions_seek_ge_unify() {
  run(|| iter_all_versions_seek_ge(SkipList::new(UNIFY_TEST_OPTIONS).unwrap()));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iter_all_versions_seek_ge_map_mut() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir
      .path()
      .join("test_skipmap_iter_all_versions_seek_ge_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    iter_all_versions_seek_ge(
      SkipList::map_mut(p, Options::new(), open_options, map_options).unwrap(),
    );
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_iter_all_versions_seek_ge_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    iter_all_versions_seek_ge(SkipList::map_anon(Options::new(), map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_iter_all_versions_seek_ge_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    iter_all_versions_seek_ge(SkipList::map_anon(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn iter_all_versions_seek_lt(l: SkipMap) {
  const N: usize = 100;

  for i in (0..N).rev() {
    let v = i * 10 + 1000;
    l.get_or_insert(&make_int_key(v), &make_value(v), trailer())
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

  l.get_or_insert(&[], &[], trailer()).unwrap();

  let ent = it.seek_upper_bound(Bound::Excluded(b""));
  assert!(ent.is_none());

  let ent = it.seek_upper_bound(Bound::Excluded(b"\x01")).unwrap();
  assert_eq!(ent.key(), &[]);
  assert_eq!(ent.value(), &[]);
}

#[test]
fn test_iter_all_versions_seek_lt() {
  run(|| iter_all_versions_seek_lt(SkipList::new(TEST_OPTIONS).unwrap()))
}

#[test]
fn test_iter_all_versions_seek_lt_unify() {
  run(|| iter_all_versions_seek_lt(SkipList::new(UNIFY_TEST_OPTIONS).unwrap()))
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iter_all_versions_seek_lt_map_mut() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir
      .path()
      .join("test_skipmap_iter_all_versions_seek_lt_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    iter_all_versions_seek_lt(
      SkipList::map_mut(p, Options::new(), open_options, map_options).unwrap(),
    );
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_iter_all_versions_seek_lt_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    iter_all_versions_seek_lt(SkipList::map_anon(Options::new(), map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_iter_all_versions_seek_lt_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    iter_all_versions_seek_lt(SkipList::map_anon(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn range(l: SkipMap) {
  for i in 1..10 {
    l.get_or_insert(&make_int_key(i), &make_value(i), trailer())
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

#[test]
fn test_range() {
  run(|| range(SkipList::new(TEST_OPTIONS).unwrap()))
}

#[test]
fn test_range_unify() {
  run(|| range(SkipList::new(UNIFY_TEST_OPTIONS).unwrap()))
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_range_map_mut() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_range_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    range(SkipList::map_mut(p, Options::new(), open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_range_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    range(SkipList::map_anon(Options::new(), map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_range_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    range(SkipList::map_anon(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn iter_latest(l: SkipMap) {
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(&make_int_key(i), &make_value(i), trailer())
      .unwrap();
  }

  for i in 50..N {
    l.insert(&make_int_key(i), &make_value(i + 1000), trailer())
      .unwrap();
  }

  for i in 0..50 {
    l.insert(&make_int_key(i), &make_value(i + 1000), trailer())
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

#[test]
fn test_iter_latest() {
  run(|| iter_latest(SkipList::new(TEST_OPTIONS).unwrap()))
}

#[test]
fn test_iter_latest_unify() {
  run(|| iter_latest(SkipList::new(UNIFY_TEST_OPTIONS).unwrap()))
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_iter_latest_map_mut() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_iter_latest_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    iter_latest(SkipList::map_mut(p, Options::new(), open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_iter_latest_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    iter_latest(SkipList::map_anon(Options::new(), map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_iter_latest_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    iter_latest(SkipList::map_anon(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn range_latest(l: SkipMap) {
  const N: usize = 100;

  for i in 0..N {
    l.get_or_insert(&make_int_key(i), &make_value(i), trailer())
      .unwrap();
  }

  for i in 50..N {
    l.insert(&make_int_key(i), &make_value(i + 1000), trailer())
      .unwrap();
  }

  for i in 0..50 {
    l.insert(&make_int_key(i), &make_value(i + 1000), trailer())
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

#[test]
fn test_range_latest() {
  run(|| range_latest(SkipList::new(TEST_OPTIONS).unwrap()))
}

#[test]
fn test_range_latest_unify() {
  run(|| range_latest(SkipList::new(UNIFY_TEST_OPTIONS).unwrap()))
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_range_latest_map_mut() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_range_latest_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    range_latest(SkipList::map_mut(p, Options::new(), open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_range_latest_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    range_latest(SkipList::map_anon(Options::new(), map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_range_latest_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    range_latest(SkipList::map_anon(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_reopen_mmap() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("reopen_skipmap");
    {
      let open_options = OpenOptions::default()
        .create(Some(ARENA_SIZE as u32))
        .read(true)
        .write(true);
      let map_options = MmapOptions::default();
      let l = SkipMap::map_mut(&p, Options::new(), open_options, map_options).unwrap();
      for i in 0..1000 {
        l.get_or_insert(&key(i), &new_value(i), trailer()).unwrap();
      }
      l.flush().unwrap();
    }

    let open_options = OpenOptions::default().read(true);
    let map_options = MmapOptions::default();
    let l = SkipMap::map(&p, Options::new(), open_options, map_options).unwrap();
    assert_eq!(1000, l.len());
    for i in 0..1000 {
      let k = key(i);
      let ent = l.get(&k).unwrap();
      assert_eq!(new_value(i), ent.value());

      assert_eq!(ent.key(), k);
    }
  })
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_reopen_mmap2() {
  run(|| unsafe {
    use rand::seq::SliceRandom;

    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("reopen_skipmap2");
    {
      let open_options = OpenOptions::default()
        .create(Some(ARENA_SIZE as u32))
        .read(true)
        .write(true);
      let map_options = MmapOptions::default();
      let l =
        SkipMap::map_mut_with_comparator(&p, Options::new(), open_options, map_options, Ascend)
          .unwrap();
      let mut data = (0..1000).collect::<Vec<usize>>();
      data.shuffle(&mut rand::thread_rng());
      for i in &data {
        let i = *i;
        l.get_or_insert(&key(i), &new_value(i), trailer()).unwrap();
      }
      l.flush_async().unwrap();

      for i in data {
        let k = key(i);
        let ent = l.get(&k).unwrap();
        assert_eq!(new_value(i), ent.value());
        assert_eq!(ent.key(), k);
      }
    }

    let open_options = OpenOptions::default().read(true);
    let map_options = MmapOptions::default();
    let l =
      SkipMap::map_with_comparator(&p, Options::new(), open_options, map_options, Ascend).unwrap();
    assert_eq!(1000, l.len());
    let mut data = (0..1000).collect::<Vec<usize>>();
    data.shuffle(&mut rand::thread_rng());
    for i in data {
      let k = key(i);
      let ent = l.get(&k).unwrap();
      assert_eq!(new_value(i), ent.value());
      assert_eq!(ent.key(), k);
    }
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

fn get_or_insert_with_value(l: SkipMap) {
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

  l.get_or_insert_with_value_builder::<()>(b"alice", vb, trailer())
    .unwrap();
}

#[test]
fn test_get_or_insert_with_value() {
  run(|| {
    get_or_insert_with_value(SkipList::new(TEST_OPTIONS).unwrap());
  })
}

#[test]
fn test_get_or_insert_with_value_unify() {
  run(|| {
    get_or_insert_with_value(SkipList::new(UNIFY_TEST_OPTIONS).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_get_or_insert_with_value_map_mut() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir
      .path()
      .join("test_skipmap_get_or_insert_with_value_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    get_or_insert_with_value(
      SkipList::map_mut(p, Options::new(), open_options, map_options).unwrap(),
    );
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_get_or_insert_with_value_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    get_or_insert_with_value(SkipList::map_anon(Options::new(), map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_get_or_insert_with_value_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    get_or_insert_with_value(SkipList::map_anon(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn get_or_insert_with(l: SkipMap) {
  let alice = Person {
    id: 1,
    name: std::string::String::from("Alice"),
  };

  let encoded_size = alice.encoded_size() as u32;

  let kb = KeyBuilder::new(5u8.into(), |key: &mut VacantBuffer| {
    key.put_slice(b"alice").unwrap();
    Ok(())
  });

  let vb = ValueBuilder::new(encoded_size, |val: &mut VacantBuffer| {
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

  l.get_or_insert_with_builders::<(), ()>(kb, vb, trailer())
    .unwrap();
}

#[test]
fn test_get_or_insert_with() {
  run(|| get_or_insert_with(SkipList::new(TEST_OPTIONS).unwrap()))
}

#[test]
fn test_get_or_insert_with_unify() {
  run(|| get_or_insert_with(SkipList::new(UNIFY_TEST_OPTIONS).unwrap()))
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_get_or_insert_with_map_mut() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_get_or_insert_with_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    get_or_insert_with(SkipList::map_mut(p, Options::new(), open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_get_or_insert_with_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    get_or_insert_with(SkipList::map_anon(Options::new(), map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_get_or_insert_with_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    get_or_insert_with(SkipList::map_anon(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn insert_in(l: SkipMap) {
  let k = 0u64.to_le_bytes();
  for i in 0..100 {
    let v = new_value(i);
    let old = l.insert(&k, &v, trailer()).unwrap();
    if let Some(old) = old {
      assert_eq!(old.key(), k);
      assert_eq!(old.value(), new_value(i - 1));
    }
  }

  let ent = l.get(&k).unwrap();
  assert_eq!(ent.key(), k);
  assert_eq!(ent.value(), new_value(99));
}

#[test]
fn test_insert_in() {
  run(|| {
    insert_in(SkipList::new(TEST_OPTIONS).unwrap());
  })
}

#[test]
fn test_insert_in_unify() {
  run(|| {
    insert_in(SkipList::new(UNIFY_TEST_OPTIONS).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_insert_in_map_mut() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_insert_in_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    insert_in(SkipList::map_mut(p, Options::new(), open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_insert_in_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    insert_in(SkipList::map_anon(Options::new(), map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_insert_in_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    insert_in(SkipList::map_anon(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn insert_with_value(l: SkipMap) {
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

  l.insert_with_value_builder::<()>(b"alice", vb, trailer())
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
    .insert_with_value_builder::<()>(b"alice", vb, trailer())
    .unwrap()
    .unwrap();

  assert_eq!(old.key(), b"alice");
  assert!(old.value().starts_with(&alice.id.to_be_bytes()));

  let ent = l.get(b"alice").unwrap();
  assert_eq!(ent.key(), b"alice");
  assert!(ent.value().starts_with(&alice2.id.to_be_bytes()));
}

#[test]
fn test_insert_with_value() {
  run(|| insert_with_value(SkipList::new(TEST_OPTIONS).unwrap()));
}

#[test]
fn test_insert_with_value_unify() {
  run(|| insert_with_value(SkipList::new(UNIFY_TEST_OPTIONS).unwrap()));
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_insert_with_value_map_mut() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir
      .path()
      .join("test_skipmap_get_or_insert_with_value_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    insert_with_value(SkipList::map_mut(p, Options::new(), open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_insert_with_value_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    insert_with_value(SkipList::map_anon(Options::new(), map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_insert_with_value_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    insert_with_value(SkipList::map_anon(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn insert_with(l: SkipMap) {
  let alice = Person {
    id: 1,
    name: std::string::String::from("Alice"),
  };

  let encoded_size = alice.encoded_size() as u32;

  let kb = KeyBuilder::new(5u8.into(), |key: &mut VacantBuffer| {
    key.put_slice(b"alice").unwrap();
    Ok(())
  });

  let vb = ValueBuilder::new(encoded_size as u32, |val: &mut VacantBuffer| {
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

  l.insert_with_builders::<(), ()>(kb, vb, trailer()).unwrap();

  let alice2 = Person {
    id: 2,
    name: std::string::String::from("Alice"),
  };

  let vb = ValueBuilder::new(encoded_size, |val: &mut VacantBuffer| {
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
    .insert_with_builders::<(), ()>(kb, vb, trailer())
    .unwrap()
    .unwrap();

  assert_eq!(old.key(), b"alice");
  assert!(old.value().starts_with(&alice.id.to_be_bytes()));

  let ent = l.get(b"alice").unwrap();
  assert_eq!(ent.key(), b"alice");
  assert!(ent.value().starts_with(&alice2.id.to_be_bytes()));
}

#[test]
fn test_insert_with() {
  run(|| insert_with(SkipList::new(TEST_OPTIONS).unwrap()))
}

#[test]
fn test_insert_with_unify() {
  run(|| insert_with(SkipList::new(UNIFY_TEST_OPTIONS).unwrap()))
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_insert_with_map_mut() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_insert_with_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    insert_with(SkipList::map_mut(p, Options::new(), open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_insert_with_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    insert_with(SkipList::map_anon(Options::new(), map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_insert_with_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    insert_with(SkipList::map_anon(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn get_or_remove(l: SkipMap) {
  for i in 0..100 {
    let v = new_value(i);
    l.insert(&key(i), &v, trailer()).unwrap();
  }

  for i in 0..100 {
    let k = key(i);
    let old = l.get_or_remove(&k, trailer()).unwrap().unwrap();
    assert_eq!(old.key(), k);
    assert_eq!(old.value(), new_value(i));

    let old = l.get_or_remove(&k, trailer()).unwrap().unwrap();
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

#[test]
fn test_get_or_remove() {
  run(|| get_or_remove(SkipList::new(TEST_OPTIONS).unwrap()))
}

#[test]
fn test_get_or_remove_unify() {
  run(|| get_or_remove(SkipList::new(UNIFY_TEST_OPTIONS).unwrap()))
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_get_or_remove_map_mut() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_get_or_remove_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    get_or_remove(SkipList::map_mut(p, Options::new(), open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_get_or_remove_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    get_or_remove(SkipList::map_anon(Options::new(), map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_get_or_remove_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    get_or_remove(SkipList::map_anon(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn remove(l: SkipMap) {
  for i in 0..100 {
    let v = new_value(i);
    l.insert(&key(i), &v, trailer()).unwrap();
  }

  for i in 0..100 {
    let k = key(i);
    // no race, remove should succeed
    let old = l
      .compare_remove(&k, trailer(), Ordering::SeqCst, Ordering::Acquire)
      .unwrap();
    assert!(old.is_none());

    // key already removed
    let old = l
      .compare_remove(&k, trailer(), Ordering::SeqCst, Ordering::Acquire)
      .unwrap();
    assert!(old.is_none());
  }

  for i in 0..100 {
    let k = key(i);
    let ent = l.get(&k);
    assert!(ent.is_none());
  }
}

#[test]
fn test_remove() {
  run(|| remove(SkipList::new(TEST_OPTIONS).unwrap()))
}

#[test]
fn test_remove_unify() {
  run(|| remove(SkipList::new(UNIFY_TEST_OPTIONS).unwrap()))
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_remove_map_mut() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_remove_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    remove(SkipList::map_mut(p, Options::new(), open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_remove_map_anon() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    remove(SkipList::map_anon(Options::new(), map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_remove_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    remove(SkipList::map_anon(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}

fn remove2(l: SkipMap) {
  for i in 0..100 {
    let v = new_value(i);
    l.insert(&key(i), &v, trailer()).unwrap();
  }

  for i in 0..100 {
    let k = key(i);
    // not found, remove should succeed
    let old = l
      .compare_remove(&k, trailer(), Ordering::SeqCst, Ordering::Acquire)
      .unwrap();
    assert!(old.is_none());

    // no-race, remove should succeed
    let old = l
      .compare_remove(&k, trailer(), Ordering::SeqCst, Ordering::Acquire)
      .unwrap();
    assert!(old.is_none());
  }

  for i in 0..100 {
    let k = key(i);
    let ent = l.get(&k);
    assert!(ent.is_none());
  }
}

#[test]
fn test_remove2() {
  run(|| remove2(SkipList::new(TEST_OPTIONS).unwrap()))
}

#[test]
fn test_remove2_unify() {
  run(|| remove2(SkipList::new(UNIFY_TEST_OPTIONS).unwrap()))
}

#[test]
#[cfg(feature = "memmap")]
#[cfg_attr(miri, ignore)]
fn test_remove2_map_mut() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_skipmap_remove2_map_mut");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE as u32))
      .read(true)
      .write(true);
    let map_options = MmapOptions::default();
    remove2(SkipList::map_mut(p, Options::new(), open_options, map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_remove2_map_anon() {
  run(|| unsafe {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    remove2(SkipList::map_anon(Options::new(), map_options).unwrap());
  })
}

#[test]
#[cfg(feature = "memmap")]
fn test_remove2_map_anon_unify() {
  run(|| {
    let map_options = MmapOptions::default().len(ARENA_SIZE as u32);
    remove2(SkipList::map_anon(UNIFY_TEST_OPTIONS, map_options).unwrap());
  })
}
