use integration::{key, new_value};
use skl::generic::{
  unique::{sync::SkipMap, Map},
  Builder,
};

fn main() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_mmap");
  {
    const N: usize = 10;

    let l = unsafe {
      Builder::new()
        .with_capacity(1 << 20)
        .with_create_new(true)
        .with_read(true)
        .with_write(true)
        .map_mut::<SkipMap<[u8], [u8]>, _>(&p)
        .unwrap()
    };

    for i in 0..N {
      let l = l.clone();
      std::thread::spawn(move || {
        l.insert(key(i).as_slice(), new_value(i).as_slice())
          .unwrap();
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
        assert_eq!(
          l.get(k.as_slice()).unwrap().value(),
          new_value(i).as_slice(),
          "broken: {i}"
        );
        drop(l);
      });
    }
    while l.refs() > 1 {
      core::hint::spin_loop();
    }
  }

  {
    const N2: usize = 10;

    let l = unsafe {
      Builder::new()
        .with_capacity(120 << 20)
        .with_read(true)
        .with_write(true)
        .map_mut::<SkipMap<[u8], [u8]>, _>(&p)
        .unwrap()
    };

    assert_eq!(N2, l.len());
    for i in 0..N2 {
      let l = l.clone();
      std::thread::spawn(move || {
        let k = key(i);
        assert_eq!(
          l.get(k.as_slice()).unwrap().value(),
          new_value(i).as_slice(),
          "broken: {i}"
        );
      });
    }
    while l.refs() > 1 {
      core::hint::spin_loop();
    }
  }
}
