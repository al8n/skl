//! A thread-safe skiplist implementation for writing memery table, SST table or something else.
//! skl-rs is a pure Rust implementation for https://github.com/dgraph-io/badger/tree/master/skl
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

/// re-export kvstructs crate
pub use kvstructs;

mod sync {
    #[cfg(not(loom))]
    pub(crate) use alloc::sync::Arc;
    #[cfg(not(loom))]
    pub(crate) use core::sync::atomic::*;

    #[cfg(all(loom, test))]
    pub(crate) use loom::sync::{atomic::*, Arc};
}
use sync::{AtomicU64, Ordering};

mod utils;

use core::mem;
use kvstructs::{bytes::Bytes, Key, KeyExt, Value};

#[derive(Debug)]
#[repr(C)]
pub(crate) struct Node {
    // Multiple parts of the value are encoded as a single uint64 so that it
    // can be atomically loaded and stored:
    //   value offset: uint32 (bits 0-31)
    //   value size  : uint16 (bits 32-63)
    pub(crate) val: AtomicU64,

    // A byte slice is 24 bytes. We are trying to save space here.
    pub(crate) key_offset: u32, // Immutable. No need to lock to access key.
    pub(crate) key_size: u16,   // Immutable. No need to lock to access key.

    // Height of the tower.
    pub(crate) height: u16,

    // Most nodes do not need to use the full height of the tower, since the
    // probability of each successive level decreases exponentially. Because
    // these elements are never accessed, they do not need to be allocated.
    // Therefore, when a node is allocated in the arena, its memory footprint
    // is deliberately truncated to not include unneeded tower elements.
    //
    // All accesses to elements should use CAS operations, with no need to lock.
    pub(crate) tower: [crate::sync::AtomicU32; Self::MAX_HEIGHT],
}

impl Node {
    /// Always align nodes on 64-bit boundaries, even on 32-bit architectures,
    /// so that the node.value field is 64-bit aligned. This is necessary because
    /// node.getValueOffset uses atomic.LoadUint64, which expects its input
    /// pointer to be 64-bit aligned.
    const NODE_ALIGN: usize = mem::size_of::<u64>() - 1;

    /// MAX_NODE_SIZE is the memory footprint of a node of maximum height.
    const MAX_NODE_SIZE: usize = mem::size_of::<Self>();

    const MAX_HEIGHT: usize = 20;

    const OFFSET_SIZE: usize = mem::size_of::<u32>();

    const HEIGHT_INCREASE: u32 = u32::MAX / 3;

    #[inline]
    fn set_val(&self, vo: u64) {
        self.val.store(vo, Ordering::SeqCst)
    }

    /// (val_offset, val_size)
    fn get_value_offset(&self) -> (u32, u32) {
        Node::decode_value(self.val.load(Ordering::SeqCst))
    }

    fn cas_next_offset(&self, height: usize, old: u32, new: u32) -> bool {
        self.tower[height]
            .compare_exchange(old, new, Ordering::SeqCst, Ordering::Relaxed)
            .is_ok()
    }

    #[inline]
    fn get_next_offset(&self, height: usize) -> u32 {
        self.tower[height].load(Ordering::SeqCst)
    }

    #[inline]
    fn encode_value(val_offset: u32, val_size: u32) -> u64 {
        ((val_size as u64) << 32) | (val_offset as u64)
    }

    /// (val_offset, val_size)
    #[inline]
    fn decode_value(value: u64) -> (u32, u32) {
        (value as u32, (value >> 32) as u32)
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
pub enum InsertResult<K: kvstructs::KeyExt, V: kvstructs::ValueExt> {
    /// Equal
    Equal(K, V),
    /// Fail to insert
    Fail(K, V),
    /// Update old value
    Update(V),
    /// Successfully inserted
    Success,
}

impl<K: kvstructs::KeyExt + Clone, V: kvstructs::ValueExt + Clone> Clone for InsertResult<K, V> {
    fn clone(&self) -> Self {
        match self {
            InsertResult::Equal(k, v) => InsertResult::Equal(k.clone(), v.clone()),
            InsertResult::Fail(k, v) => InsertResult::Fail(k.clone(), v.clone()),
            InsertResult::Update(v) => InsertResult::Update(v.clone()),
            InsertResult::Success => InsertResult::Success,
        }
    }
}

impl<K: kvstructs::KeyExt + Copy, V: kvstructs::ValueExt + Copy> Copy for InsertResult<K, V> {}

impl<K: kvstructs::KeyExt + core::fmt::Debug, V: kvstructs::ValueExt + core::fmt::Debug>
    core::fmt::Debug for InsertResult<K, V>
{
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
