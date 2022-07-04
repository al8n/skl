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
