#![doc = include_str!("../README.md")]
#![cfg_attr(not(all(feature = "std", test)), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![deny(missing_docs)]
#![allow(
  unexpected_cfgs,
  clippy::type_complexity,
  clippy::mut_from_ref,
  rustdoc::bare_urls
)]

#[cfg(not(feature = "std"))]
extern crate alloc as std;

#[cfg(feature = "std")]
extern crate std;

use core::{cmp, ops::RangeBounds};

/// A map implementation based on skiplist
pub mod map;

/// Options for the [`SkipMap`](crate::SkipMap).
pub mod options;
pub use options::Options;
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
pub use options::{MmapOptions, OpenOptions};

mod types;
pub use types::*;

pub use rarena_allocator::{Arena, Error as ArenaError};

pub use map::{AllVersionsIter, SkipMap};

const MAX_HEIGHT: usize = 32;

#[cfg(feature = "std")]
fn random_height(max_height: u8) -> u32 {
  use rand::{thread_rng, Rng};
  let mut rng = thread_rng();
  let rnd: u32 = rng.gen();
  let mut h = 1;
  let max_height = max_height as usize;

  while h < max_height && rnd <= PROBABILITIES[h] {
    h += 1;
  }
  h as u32
}

#[cfg(not(feature = "std"))]
fn random_height(max_height: u8) -> u32 {
  use rand::{rngs::OsRng, Rng};

  let max_height = max_height as usize;
  let rnd: u32 = OsRng.gen();
  let mut h = 1;

  while h < max_height && rnd <= PROBABILITIES[h] {
    h += 1;
  }
  h as u32
}

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
pub trait Comparator: core::fmt::Debug {
  /// Compares two byte slices.
  fn compare(&self, a: &[u8], b: &[u8]) -> cmp::Ordering;

  /// Returns if a is contained in range.
  fn contains<'a, Q>(&self, range: &impl RangeBounds<Q>, key: &'a [u8]) -> bool
  where
    &'a [u8]: PartialOrd<Q>,
    Q: ?Sized + PartialOrd<&'a [u8]>;
}

/// Ascend is a comparator that compares byte slices in ascending order.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Ascend;

impl Comparator for Ascend {
  #[inline]
  fn compare(&self, a: &[u8], b: &[u8]) -> cmp::Ordering {
    a.cmp(b)
  }

  #[inline]
  fn contains<'a, Q>(&self, range: &impl RangeBounds<Q>, key: &'a [u8]) -> bool
  where
    &'a [u8]: PartialOrd<Q>,
    Q: ?Sized + PartialOrd<&'a [u8]>,
  {
    range.contains(&key)
  }
}

/// Descend is a comparator that compares byte slices in descending order.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Descend;

impl Comparator for Descend {
  #[inline]
  fn compare(&self, a: &[u8], b: &[u8]) -> cmp::Ordering {
    b.cmp(a)
  }

  #[inline]
  fn contains<'a, Q>(&self, range: &impl RangeBounds<Q>, key: &'a [u8]) -> bool
  where
    &'a [u8]: PartialOrd<Q>,
    Q: ?Sized + PartialOrd<&'a [u8]>,
  {
    range.contains(&key)
  }
}

/// A trait for extra information that can be stored with entry in the skiplist.
///
/// # Safety
/// The implementors must ensure that they can be reconstructed from a byte slice directly.
/// e.g. struct includes `*const T` cannot be used as the trailer, because the pointer cannot be reconstructed from a byte slice directly.
pub unsafe trait Trailer: Copy + core::fmt::Debug {
  /// Returns the version of the trailer.
  fn version(&self) -> u64;
}

unsafe impl Trailer for u64 {
  /// Returns the version of the trailer.
  #[inline]
  fn version(&self) -> u64 {
    *self
  }
}

mod sync {
  #[cfg(not(feature = "loom"))]
  pub(crate) use core::sync::atomic::*;

  #[cfg(feature = "loom")]
  pub(crate) use loom::sync::atomic::*;
}
