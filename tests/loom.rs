#[cfg(loom)]
use skl::*;

#[cfg(loom)]
const ARENA_SIZE: usize = 1 << 20;

#[cfg(loom)]
use loom::{sync::Arc, thread};

/// Only used for testing
#[cfg(loom)]
fn key(i: usize) -> Key {
  Key::from(format!("{:05}", i)).with_ttl(0)
}

/// Only used for testing
#[cfg(loom)]
fn new_value(i: usize) -> Value {
  use bytes::{BufMut, BytesMut};

  let mut vm = BytesMut::default();
  vm.put_slice(format!("{:05}", i).as_bytes());
  Value::from(vm.freeze())
}

#[cfg(loom)]
#[cfg_attr(miri, ignore)]
#[test]
fn concurrent_write() {
  loom::model(|| {
    const N: usize = 2;
    let l = Arc::new(Skiplist::new(ARENA_SIZE));
    let wg = Arc::new(());
    for i in 0..N {
      let w = wg.clone();
      let l = l.clone();
      thread::spawn(move || {
        l.insert(key(i), new_value(i));
        drop(w);
      });
    }
    while Arc::strong_count(&wg) > 1 {}
    for i in 0..N {
      assert_eq!(
        l.get(key(i).as_key_ref()).unwrap(),
        new_value(i).as_value_ref(),
        "broken: {i}"
      );
    }
  });
}

#[cfg(loom)]
#[cfg_attr(miri, ignore)]
#[test]
fn concurrent_read() {
  loom::model(|| {
    const N: usize = 2;
    let l = Arc::new(Skiplist::new(ARENA_SIZE));
    let wg = Arc::new(());
    for i in 0..N {
      l.insert(key(i), new_value(i));
    }
    while Arc::strong_count(&wg) > 1 {}
    for i in 0..N {
      let w = wg.clone();
      let l = l.clone();
      thread::spawn(move || {
        assert_eq!(
          l.get(key(i).as_key_ref()).unwrap(),
          new_value(i).as_value_ref(),
          "broken: {i}"
        );
        drop(w);
      });
    }
  });
}
