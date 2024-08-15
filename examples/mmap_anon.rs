use skl::{u56, SkipMap};
use std::sync::Arc;

pub fn key(i: usize) -> Vec<u8> {
  format!("{:05}", i).into_bytes()
}

pub fn new_value(i: usize) -> Vec<u8> {
  format!("{:05}", i).into_bytes()
}

fn main() {
  const N: usize = 1000;

  let mmap_options = skl::MmapOptions::default().len(1 << 20);
  let l = SkipMap::map_anon(mmap_options).unwrap();
  let wg = Arc::new(());
  for i in 0..N {
    let w = wg.clone();
    let l = l.clone();
    std::thread::spawn(move || {
      l.insert(u56::new(0), &key(i), &new_value(i)).unwrap();
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
        l.get(u56::new(0), &k).unwrap().value(),
        new_value(i),
        "broken: {i}"
      );
      drop(w);
    });
  }
}
