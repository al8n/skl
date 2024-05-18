#![doc = include_str!("../README.md")]
#![cfg_attr(not(all(feature = "std", test)), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![deny(missing_docs, warnings)]
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

mod arena;

mod align8vp;
use align8vp::Pointer;

/// A map implementation based on skiplist
pub mod map;

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
mod options;
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
pub use options::{MmapOptions, OpenOptions};

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn invalid_data<E: std::error::Error + Send + Sync + 'static>(e: E) -> std::io::Error {
  std::io::Error::new(std::io::ErrorKind::InvalidData, e)
}

pub use arena::ArenaError;
pub use map::{AllVersionsIter, SkipMap};

const MAX_HEIGHT: usize = 20;

#[cfg(feature = "std")]
fn random_height() -> u32 {
  use rand::{thread_rng, Rng};
  let mut rng = thread_rng();
  let rnd: u32 = rng.gen();
  let mut h = 1;

  while h < MAX_HEIGHT && rnd <= PROBABILITIES[h] {
    h += 1;
  }
  h as u32
}

#[cfg(not(feature = "std"))]
fn random_height() -> u32 {
  use rand::{rngs::OsRng, Rng};

  let rnd: u32 = OsRng.gen();
  let mut h = 1;

  while h < MAX_HEIGHT && rnd <= PROBABILITIES[h] {
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
pub trait Comparator {
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

/// Returns when the bytes are too large to be written to the occupied value.
#[derive(Debug, Default, Clone, Copy)]
pub struct TooLarge {
  remaining: usize,
  write: usize,
}

impl core::fmt::Display for TooLarge {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    write!(
      f,
      "VacantValue does not have enough space (remaining {}, want {})",
      self.remaining, self.write
    )
  }
}

#[cfg(feature = "std")]
impl std::error::Error for TooLarge {}

/// An occupied value in the skiplist.
#[must_use = "occupied value must be fully filled with bytes."]
#[derive(Debug)]
pub struct VacantValue<'a> {
  value: &'a mut [u8],
  len: usize,
  cap: usize,
}

impl<'a> VacantValue<'a> {
  /// Write bytes to the occupied value.
  pub fn write(&mut self, bytes: &[u8]) -> Result<(), TooLarge> {
    let len = bytes.len();
    let remaining = self.cap - self.len;
    if len > remaining {
      return Err(TooLarge {
        remaining,
        write: len,
      });
    }

    self.value[self.len..self.len + len].copy_from_slice(bytes);
    self.len += len;
    Ok(())
  }

  /// Returns the capacity of the occupied value.
  #[inline]
  pub const fn capacity(&self) -> usize {
    self.cap
  }

  /// Returns the length of the occupied value.
  #[inline]
  pub const fn len(&self) -> usize {
    self.len
  }

  /// Returns `true` if the occupied value is empty.
  #[inline]
  pub const fn is_empty(&self) -> bool {
    self.len == 0
  }

  /// Returns the remaining space of the occupied value.
  #[inline]
  pub const fn remaining(&self) -> usize {
    self.cap - self.len
  }

  #[inline]
  fn new(cap: usize, value: &'a mut [u8]) -> Self {
    Self { value, len: 0, cap }
  }
}

impl<'a> core::ops::Deref for VacantValue<'a> {
  type Target = [u8];

  fn deref(&self) -> &Self::Target {
    &self.value[..self.len]
  }
}

impl<'a> core::ops::DerefMut for VacantValue<'a> {
  fn deref_mut(&mut self) -> &mut Self::Target {
    &mut self.value[..self.len]
  }
}

impl<'a> PartialEq<[u8]> for VacantValue<'a> {
  fn eq(&self, other: &[u8]) -> bool {
    self.value[..self.len].eq(other)
  }
}

impl<'a> PartialEq<VacantValue<'a>> for [u8] {
  fn eq(&self, other: &VacantValue<'a>) -> bool {
    self.eq(&other.value[..other.len])
  }
}

impl<'a> PartialEq<[u8]> for &VacantValue<'a> {
  fn eq(&self, other: &[u8]) -> bool {
    self.value[..self.len].eq(other)
  }
}

impl<'a> PartialEq<&VacantValue<'a>> for [u8] {
  fn eq(&self, other: &&VacantValue<'a>) -> bool {
    self.eq(&other.value[..other.len])
  }
}

impl<'a, const N: usize> PartialEq<[u8; N]> for VacantValue<'a> {
  fn eq(&self, other: &[u8; N]) -> bool {
    self.value[..self.len].eq(other.as_slice())
  }
}

impl<'a, const N: usize> PartialEq<VacantValue<'a>> for [u8; N] {
  fn eq(&self, other: &VacantValue<'a>) -> bool {
    self.as_slice().eq(&other.value[..other.len])
  }
}

impl<'a, const N: usize> PartialEq<&VacantValue<'a>> for [u8; N] {
  fn eq(&self, other: &&VacantValue<'a>) -> bool {
    self.as_slice().eq(&other.value[..other.len])
  }
}

impl<'a, const N: usize> PartialEq<[u8; N]> for &VacantValue<'a> {
  fn eq(&self, other: &[u8; N]) -> bool {
    self.value[..self.len].eq(other.as_slice())
  }
}

impl<'a, const N: usize> PartialEq<&mut VacantValue<'a>> for [u8; N] {
  fn eq(&self, other: &&mut VacantValue<'a>) -> bool {
    self.as_slice().eq(&other.value[..other.len])
  }
}

impl<'a, const N: usize> PartialEq<[u8; N]> for &mut VacantValue<'a> {
  fn eq(&self, other: &[u8; N]) -> bool {
    self.value[..self.len].eq(other.as_slice())
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

mod alloc {
  #[cfg(not(loom))]
  pub(crate) use std::alloc::{alloc_zeroed, dealloc, Layout};

  #[cfg(loom)]
  pub(crate) use loom::alloc::{alloc_zeroed, dealloc, Layout};
}

mod sync {
  #[derive(Debug)]
  #[repr(C)]
  pub(super) struct Link {
    pub(super) next_offset: AtomicU32,
    pub(super) prev_offset: AtomicU32,
  }

  impl Link {
    pub(super) const SIZE: usize = core::mem::size_of::<Self>();

    #[inline]
    pub(super) fn new(next_offset: u32, prev_offset: u32) -> Self {
      Self {
        next_offset: AtomicU32::new(next_offset),
        prev_offset: AtomicU32::new(prev_offset),
      }
    }
  }

  #[cfg(not(loom))]
  pub(crate) use core::sync::atomic::*;

  #[cfg(loom)]
  pub(crate) use loom::sync::atomic::*;

  #[cfg(loom)]
  pub(crate) trait AtomicMut<T> {}

  #[cfg(loom)]
  impl<T> AtomicMut<T> for AtomicPtr<T> {}

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
