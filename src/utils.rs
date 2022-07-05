use super::{HEIGHT_INCREASE, MAX_HEIGHT};

#[cfg(feature = "std")]
#[inline]
pub(crate) fn random_height() -> usize {
    use rand::{thread_rng, Rng};
    let mut rng = thread_rng();
    for h in 1..(MAX_HEIGHT - 1) {
        if !rng.gen_ratio(HEIGHT_INCREASE, u32::MAX) {
            return h;
        }
    }
    MAX_HEIGHT - 1
}

#[cfg(not(feature = "std"))]
#[inline]
pub(crate) fn random_height() -> usize {
    use rand::{rngs::OsRng, Rng, RngCore};

    for h in 1..(MAX_HEIGHT - 1) {
        if !OsRng.gen_ratio(HEIGHT_INCREASE, u32::MAX) {
            return h;
        }
    }
    MAX_HEIGHT - 1
}

#[cfg(test)]
pub(crate) fn key(i: usize) -> kvstructs::Key {
    use alloc::format;

    kvstructs::Key::from(format!("{:05}", i)).with_timestamp(0)
}

#[cfg(test)]
pub(crate) fn big_value(i: usize) -> kvstructs::Value {
    use alloc::format;
    kvstructs::Value::from(format!("{:01048576}", i))
}

#[cfg(test)]
pub(crate) fn new_value(i: usize) -> kvstructs::ValueMut {
    use alloc::format;
    use kvstructs::bytes::BufMut;

    let mut vm = kvstructs::ValueMut::default();
    vm.put_slice(format!("{:05}", i).as_bytes());
    vm
}
