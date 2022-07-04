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

mod arena;
mod fixed;
pub use crate::fixed::{FixedSKL, FixedSKLIterator, UniFixedSKLIterator};

mod growable;
pub use crate::growable::{GrowableSKL, GrowableSKLIterator, UniGrowableSKLIterator};

mod sync {
    #[cfg(not(loom))]
    pub(crate) use alloc::sync::Arc;
    #[cfg(not(loom))]
    pub(crate) use core::sync::atomic::*;

    #[cfg(all(loom, test))]
    pub(crate) use loom::sync::{atomic::*, Arc};
}

mod utils;

use core::mem;
use kvstructs::{bytes::Bytes, Key, Value};

const MAX_HEIGHT: usize = 20;
const HEIGHT_INCREASE: u32 = u32::MAX / 3;

/// MAX_NODE_SIZE is the memory footprint of a node of maximum height.
const MAX_NODE_SIZE: usize = mem::size_of::<Node>();
const OFFSET_SIZE: usize = mem::size_of::<u32>();

/// Always align nodes on 64-bit boundaries, even on 32-bit architectures,
/// so that the node.value field is 64-bit aligned. This is necessary because
/// node.getValueOffset uses atomic.LoadUint64, which expects its input
/// pointer to be 64-bit aligned.
const NODE_ALIGN: usize = mem::size_of::<u64>() - 1;

#[derive(Debug)]
#[repr(C)]
pub(crate) struct Node {
    pub(crate) key: Key,

    pub(crate) value: Bytes,

    /// height of the tower
    /// Immutable. No need to lock to height.
    pub(crate) height: u16,

    /// Most nodes do not need to use the full height of the tower, since the
    /// probability of each successive level decreases exponentially. Because
    /// these elements are never accessed, they do not need to be allocated.
    /// Therefore, when a node is allocated in the arena, its memory footprint
    /// is deliberately truncated to not include unneeded tower elements.
    ///
    /// All accesses to elements should use CAS operations, with no need to lock.
    pub(crate) tower: [sync::AtomicU32; MAX_HEIGHT],
}

impl Node {
    #[inline]
    pub(crate) fn get_next_offset(&self, h: usize) -> u32 {
        self.tower[h].load(sync::Ordering::SeqCst)
    }
}

/// Dropper
pub trait Dropper {
    /// Extra method called when dropping the ARENA memory
    fn on_drop(&mut self);
}

/// No-op [`Dropper`]
///
/// [`Dropper`]: trait.Dropper.html
#[derive(Copy, Clone, Debug, Default)]
pub struct NoopDropper;

impl Dropper for NoopDropper {
    #[inline(always)]
    fn on_drop(&mut self) {}
}

/// Insert result
#[derive(Clone)]
pub enum InsertResult {
    /// Equal
    Equal(Key, Value),
    /// Fail to insert
    Fail(Key, Value),
    /// Update old value
    Update(Value),
    /// Successfully inserted
    Success,
}

impl core::fmt::Debug for InsertResult {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            InsertResult::Equal(k, v) => f
                .debug_struct("InsertResult::Equal")
                .field("key", k)
                .field("value", v)
                .finish(),
            InsertResult::Fail(k, v) => f
                .debug_struct("InsertResult::Fail")
                .field("key", k)
                .field("value", v)
                .finish(),
            InsertResult::Update(v) => f
                .debug_struct("InsertResult::Update")
                .field("old_value", v)
                .finish(),
            InsertResult::Success => f.debug_struct("InsertResult::Success").finish(),
        }
    }
}
