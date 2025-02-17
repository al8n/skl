use integration::{big_value, key, new_value};
use skl::generic::{
  unique::{sync::SkipMap, Map},
  Builder,
};

fn main() {
  {
    const N: usize = 10;

    let l = Builder::new()
      .with_capacity(1 << 20)
      .map_anon::<SkipMap<[u8], [u8]>>()
      .unwrap();
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
    const N2: usize = 100;

    let l = Builder::new()
      .with_capacity(120 << 20)
      .map_anon::<SkipMap<[u8], [u8]>>()
      .unwrap();
    for i in 0..N2 {
      let l = l.clone();
      std::thread::spawn(move || {
        l.insert(key(i).as_slice(), big_value(i).as_slice())
          .unwrap();
      });
    }
    while l.refs() > 1 {
      core::hint::spin_loop();
    }
    assert_eq!(N2, l.len());
    for i in 0..N2 {
      let l = l.clone();
      std::thread::spawn(move || {
        let k = key(i);
        assert_eq!(
          l.get(k.as_slice()).unwrap().value(),
          big_value(i).as_slice(),
          "broken: {i}"
        );
      });
    }
    while l.refs() > 1 {
      core::hint::spin_loop();
    }
  }
}
