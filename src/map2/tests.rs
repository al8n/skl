use super::*;
use crate::{sync::Arc, badger::BadgerKey, value::badger::BadgerValue};
use alloc::format;
use bytes::{BufMut, BytesMut};

const ARENA_SIZE: usize = 1 << 20;

/// Only used for testing

pub fn key(i: usize) -> BadgerKey {
  BadgerKey::from(format!("{:05}", i)).with_version(0)
}

/// Only used for testing
pub fn big_value(i: usize) -> BadgerValue {
  BadgerValue::from(format!("{:01048576}", i))
}

/// Only used for testing
pub fn new_value(i: usize) -> BadgerValue {

  let mut vm = BytesMut::default();
  vm.put_slice(format!("{:05}", i).as_bytes());
  BadgerValue::from(vm.freeze())
}

// fn length(s: Arc<SkipMap<BadgerKey, BadgerValue>>) -> usize {
//   let head = s.get_head();
//   let mut x = s.get_next(head.0, head.1, 0);
//   let mut ctr = 0;
//   while !x.0.is_null() {
//     ctr += 1;
//     x = s.get_next(x.0, x.1, 0);
//   }
//   ctr
// }

fn test_basic_runner(l: Arc<SkipMap<BadgerKey, BadgerValue>>) {
  let mut v1 = new_value(42);
  let mut v2 = new_value(52);
  let mut v3 = new_value(62);
  let mut v4 = new_value(72);
  let mut v5 = {
    let mut vm = BytesMut::default();
    vm.put_slice(format!("{:0102400}", 1).as_bytes());
    BadgerValue::from(vm.freeze())
  };

  // Have size 100 KB which is > math.MaxUint16.
  // Try inserting values.
  v1.set_meta(55);
  eprintln!("{:?}", l.arena());
  l.insert(&BadgerKey::from("key1".as_bytes().to_vec()), &v1).unwrap();
  eprintln!("{:?}", l.arena());

  v2.set_meta(56);
  l.insert(&BadgerKey::from("key2".as_bytes()).with_version(2), &v2).unwrap();
  v3.set_meta(57);
  l.insert(&BadgerKey::from("key3".as_bytes()), &v3).unwrap();

  assert!(l.get(&BadgerKey::from("key".as_bytes())).is_none());

  let key = BadgerKey::from("key1".as_bytes());
  let v = l.get(&key).unwrap();
  assert_eq!(v.as_bytes(), "00042".as_bytes());
  assert_eq!(v.trailer().meta(), 55);
  assert!(l.get(&BadgerKey::from("key2".as_bytes())).is_none());

  let key = BadgerKey::from("key3".as_bytes());
  let v = l.get(&key).unwrap();
  assert_eq!(v.as_bytes(), "00062".as_bytes());
  assert_eq!(v.trailer().meta(), 57);

  v4.set_meta(12);
  l.insert(&BadgerKey::from("key3".as_bytes()).with_version(1), &v4).unwrap();

  let key = BadgerKey::from("key3".as_bytes()).with_version(1);
  let v = l
    .get(&key)
    .unwrap();
  assert_eq!(v.as_bytes(), "00072".as_bytes());
  assert_eq!(v.trailer().meta(), 12);

  v5.set_meta(60);
  l.insert(&BadgerKey::from("key4".as_bytes()).with_version(1), &v5.clone()).unwrap();

  let key = BadgerKey::from("key4".as_bytes()).with_version(1);
  let v = l
    .get(&key)
    .unwrap();
  assert_eq!(v.as_bytes(), v5.as_bytes());
  assert_eq!(v.trailer().meta(), 60);
}

#[test]
fn test_basic() {
  let l = Arc::new(SkipMap::<BadgerKey, BadgerValue>::new(ARENA_SIZE).unwrap());

  test_basic_runner(l);
}