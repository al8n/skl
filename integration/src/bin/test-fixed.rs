use integration::{big_value, key, new_value};
use kvstructs::ValueExt;
use skl::FixedSKL;
use std::sync::Arc;

fn main() {
    const N: usize = 1000;
    let l = FixedSKL::new(1 << 20);
    let wg = Arc::new(());
    for i in 0..N {
        let w = wg.clone();
        let l = l.clone();
        std::thread::spawn(move || {
            l.insert(key(i), new_value(i));
            drop(w);
        });
    }
    while Arc::strong_count(&wg) > 1 {}
    for i in 0..N {
        let w = wg.clone();
        let l = l.clone();
        std::thread::spawn(move || {
            assert_eq!(
                l.get(key(i)).unwrap().as_value_ref(),
                new_value(i).as_value_ref(),
                "broken: {i}"
            );
            drop(l);
            drop(w);
        });
    }
    drop(l);

    const N2: usize = 100;
    let l = FixedSKL::new(120 << 20);
    let wg = Arc::new(());
    for i in 0..N2 {
        let w = wg.clone();
        let l = l.clone();
        std::thread::spawn(move || {
            l.insert(key(i), big_value(i));
            drop(w);
        });
    }
    while Arc::strong_count(&wg) > 1 {}
    assert_eq!(N2, l.len());
    for i in 0..N2 {
        let w = wg.clone();
        let l = l.clone();
        std::thread::spawn(move || {
            assert_eq!(
                l.get(key(i)).unwrap().as_value_ref(),
                big_value(i).as_value_ref(),
                "broken: {i}"
            );
            drop(l);
            drop(w);
        });
    }
    drop(l);
}
