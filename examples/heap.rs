use skl::{sync::map::SkipMap, Builder, map::Map, Arena, Container};

pub fn key(i: usize) -> Vec<u8> {
  format!("{:05}", i).into_bytes()
}

pub fn new_value(i: usize) -> Vec<u8> {
  format!("{:05}", i).into_bytes()
}

fn main() {
  const N: usize = 1000;

  let l = Builder::new().with_capacity(1 << 20).alloc::<SkipMap>().unwrap();

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
