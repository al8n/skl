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

use core::{
  cmp,
  ops::{Bound, RangeBounds},
  ptr::NonNull,
};

/// Skiplist implementation. See [`SkipList`](base::SkipList) for more information.
mod base;
pub use base::{Entry, EntryRef, VersionedEntry, VersionedEntryRef};

mod allocator;
pub use allocator::GenericAllocator;

mod error;
pub use error::Error;

/// Implementations for concurrent environments.
mod sync;

/// Implementations for single-threaded environments.
mod unsync;

mod builder;
pub use builder::*;

mod traits;
pub use traits::{
  full, map, trailed,
  trailer::{self, Trailer},
  versioned, Arena, Container, VersionedContainer,
};

mod types;
pub use types::*;

/// Iterators for the skipmaps.
pub mod iter {
  pub use super::base::{AllVersionsIter, Iter};
}

#[cfg(any(
  all(test, not(miri)),
  all_tests,
  test_unsync_map,
  test_unsync_versioned,
  test_unsync_trailed,
  test_unsync_full,
  test_sync_full,
  test_sync_map,
  test_sync_versioned,
  test_sync_trailed,
))]
mod tests;

pub use among;
pub use dbutils::{Ascend, Comparator, Descend};
pub use either;
pub use rarena_allocator::{Allocator as ArenaAllocator, ArenaPosition, Error as ArenaError};

const MAX_HEIGHT: usize = 1 << 5;
const MIN_VERSION: Version = Version::MIN;
/// The tombstone value size, if a node's value size is equal to this value, then it is a tombstone.
const REMOVE: u32 = u32::MAX;
const DANGLING_ZST: NonNull<()> = NonNull::dangling();

/// ## Safety
/// - `T` must be a ZST.
#[inline]
const unsafe fn dangling_zst_ref<'a, T>() -> &'a T {
  #[cfg(debug_assertions)]
  if core::mem::size_of::<T>() != 0 {
    panic!("`T` must be a ZST");
  }

  // Safety: T is ZST, so it's safe to cast and deref.
  unsafe { &*(DANGLING_ZST.as_ptr() as *const T) }
}

#[cfg(feature = "std")]
fn random_height(max_height: Height) -> Height {
  use rand::{thread_rng, Rng};
  let mut rng = thread_rng();
  let rnd: u32 = rng.gen();
  let mut h = 1;
  let max_height = max_height.to_usize();

  while h < max_height && rnd <= PROBABILITIES[h] {
    h += 1;
  }
  Height::from_u8_unchecked(h as u8)
}

#[cfg(not(feature = "std"))]
fn random_height(max_height: Height) -> Height {
  use rand::{rngs::OsRng, Rng};

  let max_height = max_height.to_usize();
  let rnd: u32 = OsRng.gen();
  let mut h = 1;

  while h < max_height && rnd <= PROBABILITIES[h] {
    h += 1;
  }
  Height::from_u8_unchecked(h as u8)
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

#[inline]
const fn encode_value_pointer(offset: u32, val_size: u32) -> u64 {
  (val_size as u64) << 32 | offset as u64
}

#[inline]
const fn decode_value_pointer(value: u64) -> (u32, u32) {
  let offset = value as u32;
  let val_size = (value >> 32) as u32;
  (offset, val_size)
}

#[inline]
const fn encode_key_size_and_height(key_size: u32, height: u8) -> u32 {
  // first 27 bits for key_size, last 5 bits for height.
  key_size << 5 | height as u32
}

#[inline]
const fn decode_key_size_and_height(size: u32) -> (u32, u8) {
  let key_size = size >> 5;
  let height = (size & 0b11111) as u8;
  (key_size, height)
}

mod common {
  #[cfg(not(feature = "loom"))]
  pub(crate) use core::sync::atomic::*;

  #[cfg(feature = "loom")]
  pub(crate) use loom::sync::atomic::*;
}
