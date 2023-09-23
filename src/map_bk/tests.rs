use super::*;
use crate::{key::Key, sync::Arc, utils::*};
use alloc::format;
use bytes::{BufMut, Bytes, BytesMut};

const ARENA_SIZE: usize = 1 << 20;

fn length(s: Arc<SkipMap>) -> usize {
  let head = s.get_head();
  let mut x = s.get_next(head.0, head.1, 0);
  let mut ctr = 0;
  while !x.0.is_null() {
    ctr += 1;
    x = s.get_next(x.0, x.1, 0);
  }
  ctr
}

fn test_basic_runner(l: Arc<SkipMap>) {
  let mut v1 = new_value(42);
  let mut v2 = new_value(52);
  let mut v3 = new_value(62);
  let mut v4 = new_value(72);
  let mut v5 = {
    let mut vm = BytesMut::default();
    vm.put_slice(format!("{:0102400}", 1).as_bytes());
    Value::from(vm.freeze())
  };

  // Have size 100 KB which is > math.MaxUint16.
  // Try inserting values.
  v1.set_meta(55);
  l.insert(Key::from("key1".as_bytes().to_vec()), v1);

  v2.set_meta(56);
  l.insert(Key::from("key2".as_bytes()).with_version(2), v2);
  v3.set_meta(57);
  l.insert(Key::from("key3".as_bytes()), v3);

  assert!(l.get(KeyRef::from("key".as_bytes())).is_none());

  let v = l.get(KeyRef::from("key1".as_bytes())).unwrap();
  assert_eq!(v.value(), "00042".as_bytes().to_vec());
  assert_eq!(v.meta(), 55);
  assert!(l.get(KeyRef::from("key2".as_bytes())).is_none());

  let v = l.get(KeyRef::from("key3".as_bytes())).unwrap();
  assert_eq!(v.value(), "00062".as_bytes().to_vec());
  assert_eq!(v.meta(), 57);

  v4.set_meta(12);
  l.insert(Key::from("key3".as_bytes()).with_version(1), v4);

  let v = l
    .get(KeyRef::from("key3".as_bytes()).with_version(1))
    .unwrap();
  assert_eq!(v.value(), "00072".as_bytes().to_vec());
  assert_eq!(v.meta(), 12);

  v5.set_meta(60);
  l.insert(Key::from("key4".as_bytes()).with_version(1), v5.clone());

  let v = l
    .get(KeyRef::from("key4".as_bytes()).with_version(1))
    .unwrap();
  assert_eq!(v.value(), v5.value());
  assert_eq!(v.meta(), 60);
}

#[test]
fn test_basic() {
  let l = Arc::new(SkipMap::new(ARENA_SIZE));
  test_basic_runner(l);
}

#[test]
#[cfg_attr(miri, ignore)]
fn test_basic_mmap() {
  let l = Arc::new(SkipMap::mmap(ARENA_SIZE, tempfile::tempfile().unwrap(), true).unwrap());
  test_basic_runner(l);
}

#[test]
#[cfg_attr(miri, ignore)]
fn test_basic_mmap_anon() {
  let l = Arc::new(SkipMap::mmap_anon(ARENA_SIZE).unwrap());
  test_basic_runner(l);
}

fn test_basic_large_testcases_in(l: Arc<SkipMap>) {
  let n = 1000;

  for i in 0..n {
    l.insert(key(i), new_value(i));
  }

  for i in 0..n {
    let v = l.get(key(i).as_key_ref()).unwrap();
    assert_eq!(new_value(i).value(), v.value());
  }

  assert_eq!(n, length(l));
}

#[test]
fn test_basic_large_testcases() {
  let l = Arc::new(SkipMap::new(ARENA_SIZE));
  test_basic_large_testcases_in(l);
}

#[test]
#[cfg_attr(miri, ignore)]
fn test_basic_large_testcases_mmap() {
  let l = Arc::new(SkipMap::mmap(ARENA_SIZE, tempfile::tempfile().unwrap(), true).unwrap());
  test_basic_large_testcases_in(l);
}

#[test]
#[cfg_attr(miri, ignore)]
fn test_basic_large_testcases_mmap_anon() {
  let l = Arc::new(SkipMap::mmap_anon(ARENA_SIZE).unwrap());
  test_basic_large_testcases_in(l);
}

#[test]
fn test_concurrent_basic() {
  test_concurrent_basic_runner(Arc::new(SkipMap::new(ARENA_SIZE)));
}

#[test]
#[cfg_attr(miri, ignore)]
fn test_concurrent_basic_mmap() {
  test_concurrent_basic_runner(Arc::new(
    SkipMap::mmap(ARENA_SIZE, tempfile::tempfile().unwrap(), true).unwrap(),
  ));
}

#[test]
#[cfg_attr(miri, ignore)]
fn test_concurrent_basic_mmap_anon() {
  test_concurrent_basic_runner(Arc::new(SkipMap::mmap_anon(ARENA_SIZE).unwrap()));
}

fn test_concurrent_basic_runner(l: Arc<SkipMap>) {
  #[cfg(miri)]
  const N: usize = 100;
  #[cfg(not(miri))]
  const N: usize = 1000;

  let wg = Arc::new(());
  for i in 0..N {
    let w = wg.clone();
    let l = l.clone();
    std::thread::spawn(move || {
      l.insert(key(i), new_value(i));
      drop(w);
    });
  }
  while Arc::strong_count(&wg) > 1 {}
  for i in 0..N {
    let w = wg.clone();
    let l = l.clone();
    std::thread::spawn(move || {
      assert_eq!(
        l.get(key(i).as_key_ref()).unwrap(),
        new_value(i).as_value_ref(),
        "broken: {i}"
      );
      drop(w);
    });
  }
}

#[test]
#[cfg_attr(miri, ignore)]
fn test_concurrent_basic_big_values() {
  test_concurrent_basic_big_values_runner(Arc::new(SkipMap::new(120 << 20)));
}

#[test]
#[cfg_attr(miri, ignore)]
fn test_concurrent_basic_big_values_mmap() {
  test_concurrent_basic_big_values_runner(Arc::new(
    SkipMap::mmap(120 << 20, tempfile::tempfile().unwrap(), true).unwrap(),
  ));
}

#[test]
#[cfg_attr(miri, ignore)]
fn test_concurrent_basic_big_values_mmap_anon() {
  test_concurrent_basic_big_values_runner(Arc::new(SkipMap::mmap_anon(120 << 20).unwrap()));
}

fn test_concurrent_basic_big_values_runner(l: Arc<SkipMap>) {
  #[cfg(miri)]
  const N: usize = 10;
  #[cfg(not(miri))]
  const N: usize = 100;

  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      l.insert(key(i), big_value(i));
    });
  }
  while Arc::strong_count(&l) > 1 {}
  assert_eq!(N, l.len());
  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      assert_eq!(
        l.get(key(i).as_key_ref()).unwrap(),
        big_value(i).as_value_ref(),
        "broken: {i}"
      );
    });
  }
  while Arc::strong_count(&l) > 1 {}
}

fn assert_find_near_not_null(
  l: Arc<SkipMap>,
  less: bool,
  allow_equal: bool,
  fk: Key,
  ek: Key,
  is_eq: bool,
) {
  let (n, _, eq) = l.find_near(fk.as_key_ref(), less, allow_equal);
  unsafe {
    let n = &*n;
    let key = l.arena.get_key(n.key_offset, n.key_size, n.timestamped());
    assert!(key.eq(&ek));
  }
  assert_eq!(is_eq, eq);
}

fn assert_find_near_null(l: Arc<SkipMap>, less: bool, allow_equal: bool, fk: Key) {
  let (n, _, eq) = l.find_near(fk.as_key_ref(), less, allow_equal);
  assert!(n.is_null());
  assert!(!eq);
}

#[test]
fn test_find_near() {
  let l = Arc::new(SkipMap::new(ARENA_SIZE));
  for i in 0..1000 {
    let k = Key::from(format!("{:05}", i * 10 + 5));
    l.insert(k, new_value(i));
  }

  assert_find_near_not_null(
    l.clone(),
    false,
    false,
    Key::from("00001"),
    Key::from("00005"),
    false,
  );

  assert_find_near_not_null(
    l.clone(),
    false,
    true,
    Key::from("00001"),
    Key::from("00005"),
    false,
  );

  assert_find_near_null(l.clone(), true, false, Key::from("00001"));

  assert_find_near_null(l.clone(), true, true, Key::from("00001"));

  assert_find_near_not_null(
    l.clone(),
    false,
    false,
    Key::from("00005"),
    Key::from("00015"),
    false,
  );

  assert_find_near_not_null(
    l.clone(),
    false,
    true,
    Key::from("00005"),
    Key::from("00005"),
    true,
  );

  assert_find_near_null(l.clone(), true, false, Key::from("00005"));

  assert_find_near_not_null(
    l.clone(),
    true,
    true,
    Key::from("00005"),
    Key::from("00005"),
    true,
  );

  assert_find_near_not_null(
    l.clone(),
    false,
    false,
    Key::from("05555"),
    Key::from("05565"),
    false,
  );

  assert_find_near_not_null(
    l.clone(),
    false,
    true,
    Key::from("05555"),
    Key::from("05555"),
    true,
  );

  assert_find_near_not_null(
    l.clone(),
    true,
    false,
    Key::from("05555"),
    Key::from("05545"),
    false,
  );

  assert_find_near_not_null(
    l.clone(),
    true,
    true,
    Key::from("05555"),
    Key::from("05555"),
    true,
  );

  assert_find_near_not_null(
    l.clone(),
    false,
    false,
    Key::from("05558"),
    Key::from("05565"),
    false,
  );

  assert_find_near_not_null(
    l.clone(),
    false,
    true,
    Key::from("05558"),
    Key::from("05565"),
    false,
  );

  assert_find_near_not_null(
    l.clone(),
    true,
    false,
    Key::from("05558"),
    Key::from("05555"),
    false,
  );

  assert_find_near_not_null(
    l.clone(),
    true,
    true,
    Key::from("05558"),
    Key::from("05555"),
    false,
  );

  assert_find_near_null(l.clone(), false, false, Key::from("09995"));

  assert_find_near_not_null(
    l.clone(),
    false,
    true,
    Key::from("09995"),
    Key::from("09995"),
    true,
  );

  assert_find_near_not_null(
    l.clone(),
    true,
    false,
    Key::from("09995"),
    Key::from("09985"),
    false,
  );

  assert_find_near_not_null(
    l.clone(),
    true,
    false,
    Key::from("09995"),
    Key::from("09985"),
    false,
  );

  assert_find_near_null(l.clone(), false, false, Key::from("59995"));

  assert_find_near_null(l.clone(), false, true, Key::from("59995"));

  assert_find_near_not_null(
    l.clone(),
    true,
    false,
    Key::from("59995"),
    Key::from("09995"),
    false,
  );

  assert_find_near_not_null(
    l.clone(),
    true,
    true,
    Key::from("59995"),
    Key::from("09995"),
    false,
  );
}

// test_iter_next tests a basic iteration over all nodes from the beginning.
#[test]
fn test_iter_next() {
  let n = 100;
  let l = Arc::new(SkipMap::new(ARENA_SIZE));
  let mut iter = l.iter();
  assert!(!iter.valid());
  iter.seek_to_first();
  assert!(!iter.valid());
  for i in (0..n).rev() {
    l.insert(Key::from(format!("{:05}", i)), new_value(i));
  }
  iter.seek_to_first();
  for i in 0..n {
    assert!(iter.valid());
    let v = iter.value();
    assert_eq!(new_value(i), v);
    iter.next();
  }

  assert!(!iter.valid());
}

// test_iter_prev tests a basic iteration over all nodes from the beginning.
#[test]
fn test_iter_prev() {
  let n = 100;
  let l = Arc::new(SkipMap::new(ARENA_SIZE));
  let mut iter = l.iter();
  assert!(!iter.valid());
  iter.seek_to_first();
  assert!(!iter.valid());
  for i in 0..n {
    l.insert(Key::from(format!("{:05}", i)), new_value(i));
  }

  iter.seek_to_last();
  for i in (0..n).rev() {
    assert!(iter.valid());
    let v = iter.value();
    assert_eq!(new_value(i), v);
    iter.prev();
  }

  assert!(!iter.valid());
}

fn assert_seek(iter: &mut SkipMapIterator, seek_to: &'static str) {
  iter.seek(KeyRef::from(seek_to));
  assert!(iter.valid());
  assert_eq!(iter.value().value(), Bytes::from(seek_to));
}

fn assert_seek_null(iter: &mut SkipMapIterator, seek_to: &'static str) {
  iter.seek(KeyRef::from(seek_to));
  assert!(!iter.valid());
}

#[test]
fn test_iter_seek() {
  let n = 100;
  let l = Arc::new(SkipMap::new(ARENA_SIZE));
  let mut iter = l.iter();
  assert!(!iter.valid());
  iter.seek_to_first();
  assert!(!iter.valid());

  for i in (0..n).rev() {
    let v = i * 10 + 1000;
    l.insert(Key::from(format!("{:05}", v)), new_value(v));
  }

  iter.seek_to_first();
  assert!(iter.valid());
  assert_eq!(iter.value().value(), Bytes::from("01000"));

  iter.seek(KeyRef::from("01000"));
  assert!(iter.valid());
  assert_eq!(iter.value().value(), Bytes::from("01000"));

  iter.seek(KeyRef::from("01005"));
  assert!(iter.valid());
  assert_eq!(iter.value().value(), Bytes::from("01010"));

  assert_seek(&mut iter, "01010");
  assert_seek_null(&mut iter, "99999");

  // Try seek for prev
  iter.seek_for_prev(KeyRef::from("00"));
  assert!(!iter.valid());

  iter.seek_for_prev(KeyRef::from("01000"));
  assert!(iter.valid());
  assert_eq!(iter.value().value(), Bytes::from("01000"));

  iter.seek_for_prev(KeyRef::from("01005"));
  assert!(iter.valid());
  assert_eq!(iter.value().value(), Bytes::from("01000"));

  iter.seek_for_prev(KeyRef::from("01010"));
  assert!(iter.valid());
  assert_eq!(iter.value().value(), Bytes::from("01010"));

  iter.seek_for_prev(KeyRef::from("99999"));
  assert!(iter.valid());
  assert_eq!(iter.value().value(), Bytes::from("01990"));
}
