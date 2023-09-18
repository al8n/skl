use skl::{Key, SkipMap, Value};
use std::sync::Arc;

pub fn key(i: usize) -> Key {
  Key::from(format!("{:05}", i))
}

pub fn new_value(i: usize) -> Value {
  use bytes::{BufMut, BytesMut};

  let mut vm = BytesMut::default();
  vm.put_slice(format!("{:05}", i).as_bytes());
  Value::from(vm.freeze())
}

fn main() {
  const N: usize = 1000;
  let l = Arc::new(SkipMap::mmap_anon(1 << 20).unwrap());
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
