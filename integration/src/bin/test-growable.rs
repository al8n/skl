use integration::{big_value, key, new_value};
use kvstructs::ValueExt;
use skl::GrowableSKL;

fn main() {
    const N: usize = 1000;
    let l = GrowableSKL::new(20);
    for i in 0..N {
        let l = l.clone();
        l.insert(key(i), new_value(i));
    }
    for i in 0..N {
        let l = l.clone();
        assert_eq!(
            l.get(key(i)).unwrap().as_value_ref(),
            new_value(i).as_value_ref(),
            "broken: {i}"
        );
    }

    const N2: usize = 100;
    let l = GrowableSKL::new(20);
    for i in 0..N2 {
        let l = l.clone();
        l.insert(key(i), big_value(i));
    }

    assert_eq!(N2, l.len());
    for i in 0..N2 {
        let l = l.clone();
        assert_eq!(
            l.get(key(i)).unwrap().as_value_ref(),
            big_value(i).as_value_ref(),
            "broken: {i}"
        );
    }
}
