use integration::{big_value, key, new_value};
use skl::*;
use std::sync::Arc;

fn main() {
  {
    const N: usize = 1000;
    let l = Arc::new(SkipMap::new(1 << 20).unwrap());
    for i in 0..N {
      let l = l.clone();
      std::thread::spawn(move || {
        l.insert(0, &key(i), &new_value(i)).unwrap();
        drop(l);
      });
    }
    while Arc::strong_count(&l) > 1 {}
    for i in 0..N {
      let l = l.clone();
      std::thread::spawn(move || {
        let k = key(i);
        assert_eq!(l.get(0, &k).unwrap().value(), new_value(i), "broken: {i}");
        drop(l);
      });
    }
    while Arc::strong_count(&l) > 1 {}
  }

  {
    const N2: usize = 100;
    let l = Arc::new(SkipMap::new(120 << 20).unwrap());
    for i in 0..N2 {
      let l = l.clone();
      std::thread::spawn(move || {
        l.insert(0, &key(i), &big_value(i)).unwrap();
      });
    }
    while Arc::strong_count(&l) > 1 {}
    assert_eq!(N2, l.len());
    for i in 0..N2 {
      let l = l.clone();
      std::thread::spawn(move || {
        let k = key(i);
        assert_eq!(l.get(0, &k).unwrap().value(), big_value(i), "broken: {i}");
      });
    }
    while Arc::strong_count(&l) > 1 {}
  }
}
