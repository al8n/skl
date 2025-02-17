use skl::dynamic::{
  unique::{sync::SkipMap, Map},
  Builder,
};

pub fn key(i: usize) -> Vec<u8> {
  format!("{:05}", i).into_bytes()
}

pub fn new_value(i: usize) -> Vec<u8> {
  format!("{:05}", i).into_bytes()
}

fn main() {
  const N: usize = 1000;

  let l = unsafe {
    Builder::new()
      .with_capacity(1 << 20)
      .with_read(true)
      .with_write(true)
      .with_create_new(true)
      .map_mut::<SkipMap, _>("test.wal")
      .unwrap()
  };

  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      l.insert(key(i).as_slice(), new_value(i).as_slice())
        .unwrap();
    });
  }

  while l.refs() > 1 {}

  for i in 0..N {
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
}
