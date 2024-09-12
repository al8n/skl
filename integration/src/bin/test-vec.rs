use integration::{big_value, key, new_value};
use skl::{sync::map::SkipMap, *};

fn main() {
  {
    const N: usize = 10;
    let l = SkipMap::new(Options::new().with_capacity(1 << 20)).unwrap();
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
    let l = SkipMap::new(Options::new().with_capacity(120 << 20)).unwrap();
    for i in 0..N2 {
      let l = l.clone();
      std::thread::spawn(move || {
        l.insert(&key(i), &big_value(i)).unwrap();
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
        assert_eq!(l.get(&k).unwrap().value(), big_value(i), "broken: {i}");
      });
    }
    while l.refs() > 1 {
      core::hint::spin_loop();
    }
  }
}
