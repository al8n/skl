use skl::SkipMap;
use std::sync::Arc;

pub fn key(i: usize) -> Vec<u8> {
  format!("{:05}", i).into_bytes()
}

pub fn new_value(i: usize) -> Vec<u8> {
  format!("{:05}", i).into_bytes()
}
fn main() {
  const N: usize = 1000;

  let mmap_options = skl::MmapOptions::default();
  let open_options = skl::OpenOptions::default()
    .create_new(Some(1 << 20))
    .read(true)
    .write(true);

  let l = SkipMap::mmap_mut("test.wal", open_options, mmap_options).unwrap();
  let wg = Arc::new(());
  for i in 0..N {
    let w = wg.clone();
    let l = l.clone();
    std::thread::spawn(move || {
      l.insert(0, &key(i), &new_value(i)).unwrap();
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
