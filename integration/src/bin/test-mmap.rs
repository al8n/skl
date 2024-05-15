use integration::{key, new_value};
use skl::*;
use std::sync::Arc;

fn main() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_mmap");
  {
    const N: usize = 10;

    let open_options = OpenOptions::default()
      .create_new(Some(1 << 20))
      .read(true)
      .write(true);
    let mmap_options = MmapOptions::default();
    let l = Arc::new(SkipMap::mmap_mut(&p, open_options, mmap_options).unwrap());
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
    const N2: usize = 10;

    let open_options = OpenOptions::default().read(true);
    let mmap_options = MmapOptions::default();
    let l = Arc::new(SkipMap::<u64>::mmap(&p, open_options, mmap_options).unwrap());
    assert_eq!(N2, l.len());
    for i in 0..N2 {
      let l = l.clone();
      std::thread::spawn(move || {
        let k = key(i);
        assert_eq!(l.get(0, &k).unwrap().value(), new_value(i), "broken: {i}");
      });
    }
    while Arc::strong_count(&l) > 1 {}
  }
}
