use skl::{sync::map::SkipMap, Options};

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

  let l =
    unsafe { SkipMap::map_mut("test.wal", Options::new(), open_options, mmap_options).unwrap() };
  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      l.insert(&key(i), &new_value(i)).unwrap();
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
