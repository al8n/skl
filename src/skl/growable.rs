use crossbeam_epoch as epoch;
use crossbeam_skiplist::SkipMap;
use kvstructs::{Key, Value};
use kvstructs::raw_pointer::RawKeyPointer;
use crate::{Dropper, NoopDropper};
use crate::skl::fixed::SKL;
use crate::skl::MAX_NODE_SIZE;

const EXP_FACTOR: usize = 2;

pub struct GrowableSKL<D: Dropper + Clone> {
    list: SkipMap<RawKeyPointer, SKL<NoopDropper>>,
    cap: usize,
    dropper: D,
}

impl GrowableSKL<NoopDropper> {
    pub fn new() -> Self {
        Self {
            list: SkipMap::new(),
            cap: MAX_NODE_SIZE * EXP_FACTOR,
            dropper: NoopDropper::default(),
        }
    }
}

impl<D: Dropper + Clone> GrowableSKL<D> {

    pub fn insert(&self, k: Key, v: Value) {
        if self.list.is_empty() {
            let skl = SKL::new_with_dropper(self.cap * 2, self.dropper.clone());
            skl.insert(k, v);
        }
    }
}


