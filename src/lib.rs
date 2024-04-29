#![doc = include_str!("../README.md")]
#![cfg_attr(not(all(feature = "std", test)), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![deny(missing_docs)]
#![allow(clippy::type_complexity, clippy::mut_from_ref)]

#[cfg(not(feature = "std"))]
extern crate alloc as std;

#[cfg(feature = "std")]
extern crate std;

use ::core::{cmp, mem};
use core::ops::RangeBounds;

mod arena;
/// A map implementation based on skiplist
pub mod map;

/// A set implementation based on skiplist
pub mod set;

pub use arena::{Arena, ArenaError};
pub use map::{MapIterator, SkipMap};
// pub use set::{SetIterator, SkipSet};

const MAX_HEIGHT: usize = 20;
const NODE_ALIGNMENT_FACTOR: usize = mem::align_of::<u32>();

/// Precompute the skiplist probabilities so that only a single random number
/// needs to be generated and so that the optimal pvalue can be used (inverse
/// of Euler's number).
const PROBABILITIES: [u32; MAX_HEIGHT] = {
  const P: f64 = 1.0 / core::f64::consts::E;

  let mut probabilities = [0; MAX_HEIGHT];
  let mut p = 1f64;

  let mut i = 0;
  while i < MAX_HEIGHT {
    probabilities[i] = ((u32::MAX as f64) * p) as u32;
    p *= P;
    i += 1;
  }

  probabilities
};

/// Comparator is used for key-value database developers to define their own key comparison logic.
/// e.g. some key-value database developers may want to alpabetically comparation
pub trait Comparator: Clone {
  /// Compares two byte slices.
  fn compare(&self, a: &[u8], b: &[u8]) -> cmp::Ordering;

  /// Returns if a is contained in range.
  fn contains(&self, range: &impl RangeBounds<[u8]>, key: &[u8]) -> bool;

  /// Compares two u64 values.
  fn compare_trailer(&self, a: u64, b: u64) -> cmp::Ordering;
}

impl Comparator for () {
  #[inline]
  fn compare(&self, a: &[u8], b: &[u8]) -> cmp::Ordering {
    a.cmp(b)
  }

  #[inline]
  fn contains(&self, range: &impl RangeBounds<[u8]>, key: &[u8]) -> bool {
    range.contains(key)
  }

  #[inline]
  fn compare_trailer(&self, a: u64, b: u64) -> cmp::Ordering {
    a.cmp(&b)
  }
}

/// Re-export bytes crate
pub use bytes;

mod sync {
  #[cfg(not(loom))]
  pub(crate) use core::sync::atomic::*;
  #[cfg(all(not(loom), test))]
  pub(crate) use std::sync::Arc;

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
