use skl::generic::{
  multiple_version::{sync::SkipMap, Map},
  Builder,
};

pub fn key(i: usize) -> String {
  format!("{:05}", i)
}

pub fn new_value(i: usize) -> String {
  format!("{:05}", i)
}

fn main() {
  const N: usize = 1000;

  let l = Builder::new()
    .with_capacity(1 << 20)
    .alloc::<SkipMap<str, str>>()
    .unwrap();

  for i in 0..(N / 2) {
    let l = l.clone();
    std::thread::spawn(move || {
      l.insert(0, key(i).as_str(), new_value(i).as_str()).unwrap();
    });
  }

  for i in (N / 2)..N {
    let l = l.clone();
    std::thread::spawn(move || {
      l.insert(1, key(i).as_str(), new_value(i).as_str()).unwrap();
    });
  }

  while l.refs() > 1 {}

  for i in 0..N {
    let l = l.clone();
    std::thread::spawn(move || {
      let k = key(i);
      assert_eq!(
        l.get(2, k.as_str()).unwrap().value(),
        new_value(i).as_str(),
        "broken: {i}"
      );
    });
  }
}
