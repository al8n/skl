use integration::{key, new_value};
use skl::{map::SkipMap, *};

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
    let l = SkipMap::map_mut(&p, open_options, mmap_options).unwrap();
    for i in 0..N {
      let l = l.clone();
      std::thread::spawn(move || {
        l.insert(&key(i), &new_value(i)).unwrap();
        drop(l);
      });
    }
    while l.refs() > 1 {
      core::hint::spin_loop();
    }
    for i in 0..N {
      let l = l.clone();
      std::thread::spawn(move || {
        let k = key(i);
        assert_eq!(l.get(&k).unwrap().value(), new_value(i), "broken: {i}");
        drop(l);
      });
    }
    while l.refs() > 1 {
      core::hint::spin_loop();
    }
  }

  {
    const N2: usize = 10;

    let open_options = OpenOptions::default().read(true);
    let mmap_options = MmapOptions::default();
    let l = SkipMap::map(&p, open_options, mmap_options, 0).unwrap();
    assert_eq!(N2, l.len());
    for i in 0..N2 {
      let l = l.clone();
      std::thread::spawn(move || {
        let k = key(i);
        assert_eq!(l.get(&k).unwrap().value(), new_value(i), "broken: {i}");
      });
    }
    while l.refs() > 1 {
      core::hint::spin_loop();
    }
  }
}
