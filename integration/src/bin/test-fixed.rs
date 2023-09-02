use integration::{big_value, key, new_value};
use skl::*;
use std::sync::Arc;

fn main() {
    {
        const N: usize = 1000;
        let l = Arc::new(Skiplist::new(1 << 20));
        for i in 0..N {
            let l = l.clone();
            std::thread::spawn(move || {
                l.insert(key(i), new_value(i));
                drop(l);
            });
        }
        while Arc::strong_count(&l) > 1 {}
        for i in 0..N {
            let l = l.clone();
            std::thread::spawn(move || {
                assert_eq!(
                    l.get(key(i).as_key_ref()).unwrap(),
                    new_value(i).as_value_ref(),
                    "broken: {i}"
                );
                drop(l);
            });
        }
        while Arc::strong_count(&l) > 1 {}
      }
    
      {
        const N2: usize = 100;
        let l = Arc::new(Skiplist::new(120 << 20));
        for i in 0..N2 {
            let l = l.clone();
            std::thread::spawn(move || {
                l.insert(key(i), big_value(i));
            });
        }
        while Arc::strong_count(&l) > 1 {}
        assert_eq!(N2, l.len());
        for i in 0..N2 {
            let l = l.clone();
            std::thread::spawn(move || {
                assert_eq!(
                    l.get(key(i).as_key_ref()).unwrap(),
                    big_value(i).as_value_ref(),
                    "broken: {i}"
                );
            });
        }
        while Arc::strong_count(&l) > 1 {}
      }
}
