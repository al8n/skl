use super::*;
use ::loom::{sync::Arc, thread};

const ARENA_SIZE: usize = 1 << 20;

/// Only used for testing
fn key(i: usize) -> Vec<u8> {
  format!("{:05}", i).into_bytes()
}

/// Only used for testing
fn new_value(i: usize) -> Vec<u8> {
  format!("{:05}", i).into_bytes()
}

#[test]
fn concurrent_write() {
  ::loom::model(|| {
    const N: usize = 2;
    let l = Arc::new(SkipMap::new(ARENA_SIZE).unwrap());
    let wg = Arc::new(());
    for i in 0..N {
      let w = wg.clone();
      let l = l.clone();
      thread::spawn(move || {
        l.insert(0, &key(i), &new_value(i)).unwrap();
        drop(w);
      });
    }
    while Arc::strong_count(&wg) > 1 {}
    for i in 0..N {
      assert_eq!(
        l.get(0, &key(i)).unwrap().value(),
        new_value(i),
        "broken: {i}"
      );
    }
  });
}

#[test]
fn concurrent_read() {
  ::loom::model(|| {
    const N: usize = 2;
    let l = Arc::new(SkipMap::new(ARENA_SIZE).unwrap());
    let wg = Arc::new(());
    for i in 0..N {
      l.insert(0, &key(i), &new_value(i)).unwrap();
    }
    while Arc::strong_count(&wg) > 1 {}
    for i in 0..N {
      let w = wg.clone();
      let l = l.clone();
      thread::spawn(move || {
        assert_eq!(
          l.get(0, &key(i)).unwrap().value(),
          new_value(i),
          "broken: {i}"
        );
        drop(w);
      });
    }
  });
}
