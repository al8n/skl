//! A template for creating Rust open-source repo on GitHub
//!
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![deny(missing_docs)]
#![allow(warnings)]

extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

mod skl;
pub use crate::skl::{Dropper, NoopDropper, SKL};

use core::mem;

mod sync {
    #[cfg(not(target_feature = "skl_loom"))]
    pub(crate) use alloc::sync::Arc;
    #[cfg(not(target_feature = "skl_loom"))]
    pub(crate) use core::sync::atomic::{AtomicU32, AtomicUsize, Ordering};

    #[cfg(target_feature = "skl_loom")]
    pub(crate) use loom_crate::sync::{
        atomic::{AtomicU32, AtomicUsize, Ordering},
        Arc,
    };
}
