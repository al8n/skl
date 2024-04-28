#![doc = include_str!("../README.md")]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![deny(missing_docs)]
#![allow(clippy::type_complexity, clippy::mut_from_ref)]

extern crate alloc;

#[cfg(feature = "std")]
extern crate std;

mod arena;
/// A map implementation based on skiplist
pub mod map;
mod node;

// /// A set implementation based on skiplist
// pub mod set;

pub use arena::{Arena, ArenaError};
pub use map::{MapIterator, SkipMap};
// pub use set::{SetIterator, SkipSet};

const MAX_HEIGHT: usize = 20;
const NODE_ALIGNMENT_FACTOR: usize = core::mem::align_of::<u32>();

/// Comparator is used for key-value database developers to define their own key comparison logic.
/// e.g. some key-value database developers may want to alpabetically comparation
pub trait Comparator: Clone {
  /// Compares two byte slices.
  fn compare(&self, a: &[u8], b: &[u8]) -> core::cmp::Ordering;
}

impl Comparator for () {
  #[inline]
  fn compare(&self, a: &[u8], b: &[u8]) -> core::cmp::Ordering {
    a.cmp(b)
  }
}

/// Re-export bytes crate
pub use bytes;

mod sync {
  #[cfg(all(not(loom), test))]
  pub(crate) use alloc::sync::Arc;
  #[cfg(not(loom))]
  pub(crate) use core::sync::atomic::*;

  #[cfg(loom)]
  pub(crate) use loom::sync::{atomic::*, Arc};

  #[cfg(loom)]
  pub(crate) trait AtomicMut<T> {}

  #[cfg(not(loom))]
  pub(crate) trait AtomicMut<T> {
    fn with_mut<F, R>(&mut self, f: F) -> R
    where
      F: FnOnce(&mut *mut T) -> R;
  }

  #[cfg(not(loom))]
  impl<T> AtomicMut<T> for AtomicPtr<T> {
    fn with_mut<F, R>(&mut self, f: F) -> R
    where
      F: FnOnce(&mut *mut T) -> R,
    {
      f(self.get_mut())
    }
  }
}
