use skl::{
  generic::{
    unique::{sync::SkipMap, Map},
    Ascend, Builder,
  },
  Arena,
};

pub fn key(i: usize) -> Vec<u8> {
  format!("{:05}", i).into_bytes()
}

pub fn new_value(i: usize) -> Vec<u8> {
  format!("{:05}", i).into_bytes()
}

/// This example demonstrates how to create multiple SkipMaps on the same ARENA allocator.
fn main() {
  unsafe {
    let header = {
      let l = Builder::new()
        .with_create_new(true)
        .with_read(true)
        .with_write(true)
        .with_capacity(1024 * 1024)
        .map_mut::<SkipMap<[u8], [u8]>, _>("multiple_maps.wal")
        .unwrap();
      let l2 =
        SkipMap::<[u8], [u8]>::create_from_allocator(l.allocator().clone(), Ascend::new()).unwrap();
      let h2 = l2.header().copied().unwrap();

      let t1 = std::thread::spawn(move || {
        for i in 0..500 {
          l.get_or_insert(key(i).as_slice(), new_value(i).as_slice())
            .unwrap();
        }
        l.flush().unwrap();
      });

      let t2 = std::thread::spawn(move || {
        for i in 500..1000 {
          l2.get_or_insert(key(i).as_slice(), new_value(i).as_slice())
            .unwrap();
        }
        l2.flush().unwrap();
      });

      t1.join().unwrap();
      t2.join().unwrap();

      h2
    };

    let l = Builder::new()
      .with_read(true)
      .with_write(true)
      .with_capacity((1024 * 1024 * 2) as u32)
      .map_mut::<SkipMap<[u8], [u8]>, _>("multiple_maps.wal")
      .unwrap();
    let l2 =
      SkipMap::<[u8], [u8]>::open_from_allocator(header, l.allocator().clone(), Ascend::new())
        .unwrap();
    assert_eq!(500, l.len());
    assert_eq!(500, l2.len());

    for i in 0..500 {
      let k = key(i);
      let ent = l.get(k.as_slice()).unwrap();
      assert_eq!(new_value(i).as_slice(), ent.value());
      assert_eq!(ent.key(), k.as_slice());
    }

    for i in 500..1000 {
      let k = key(i);
      let ent = l2.get(k.as_slice()).unwrap();
      assert_eq!(new_value(i).as_slice(), ent.value());
      assert_eq!(ent.key(), k.as_slice());
    }
  }
}
