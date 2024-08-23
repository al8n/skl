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
};

/// A versioned skipmap implementation.
pub mod versioned;

/// A versioned skipmap implementation with trailer support.
pub mod trailed;

/// Skiplist implementation.
pub mod base;

/// A skipmap based on the [`SkipList`](base::SkipList).
pub mod map;

/// Options for the [`SkipMap`](crate::SkipMap).
pub mod options;
pub use options::Options;
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
pub use options::{MmapOptions, OpenOptions};

mod types;
pub use types::*;

pub use base::{AllVersionsIter, KeyBuilder, UnlinkedNode, ValueBuilder};
pub use either;
pub use rarena_allocator::{sync::Arena, ArenaPosition, Error as ArenaError};

const MAX_HEIGHT: usize = 1 << 5;
const MIN_VERSION: Version = Version::MIN;

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

/// Comparator is used for key-value database developers to define their own key comparison logic.
/// e.g. some key-value database developers may want to alpabetically comparation
pub trait Comparator: core::fmt::Debug {
  /// Compares two byte slices.
  fn compare(&self, a: &[u8], b: &[u8]) -> cmp::Ordering;

  /// Returns if a is contained in range.
  fn contains(&self, start_bound: Bound<&[u8]>, end_bound: Bound<&[u8]>, key: &[u8]) -> bool;
}

impl<C: Comparator> Comparator for std::sync::Arc<C> {
  #[inline]
  fn compare(&self, a: &[u8], b: &[u8]) -> cmp::Ordering {
    (**self).compare(a, b)
  }

  fn contains(&self, start_bound: Bound<&[u8]>, end_bound: Bound<&[u8]>, key: &[u8]) -> bool {
    (**self).contains(start_bound, end_bound, key)
  }
}

impl<C: Comparator> Comparator for std::rc::Rc<C> {
  #[inline]
  fn compare(&self, a: &[u8], b: &[u8]) -> cmp::Ordering {
    (**self).compare(a, b)
  }

  fn contains(&self, start_bound: Bound<&[u8]>, end_bound: Bound<&[u8]>, key: &[u8]) -> bool {
    (**self).contains(start_bound, end_bound, key)
  }
}

impl<C: Comparator> Comparator for std::boxed::Box<C> {
  #[inline]
  fn compare(&self, a: &[u8], b: &[u8]) -> cmp::Ordering {
    (**self).compare(a, b)
  }

  fn contains(&self, start_bound: Bound<&[u8]>, end_bound: Bound<&[u8]>, key: &[u8]) -> bool {
    (**self).contains(start_bound, end_bound, key)
  }
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
  fn contains(&self, start_bound: Bound<&[u8]>, end_bound: Bound<&[u8]>, key: &[u8]) -> bool {
    (start_bound, end_bound).contains(&key)
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
  fn contains(&self, start_bound: Bound<&[u8]>, end_bound: Bound<&[u8]>, key: &[u8]) -> bool {
    (start_bound, end_bound).contains(&key)
  }
}

/// A trait for extra information that can be stored with entry in the skiplist.
///
/// # Safety
/// - The implementors must ensure that they can be reconstructed from a byte slice directly.
///   e.g. struct includes `*const T` cannot be used as the trailer, because the pointer is invalid
///   after restart the program.
/// - The implementors must ensure that they can be safely convert from `*const [u8]` to `*const T`
pub unsafe trait Trailer: core::fmt::Debug {
  /// Returns `true` if the trailer is valid. If a trailer is not valid, it will be ignored when
  /// read or iterated, but users can still access such entry through `get_versioned` or `iter_all_versions`.
  fn is_valid(&self) -> bool;
}

macro_rules! dummy_trailer {
  ($($t:ty),+ $(,)?) => {
    $(
      unsafe impl Trailer for $t {
        #[inline]
        fn is_valid(&self) -> bool {
          true
        }
      }

      unsafe impl<const N: usize> Trailer for [$t; N] {
        #[inline]
        fn is_valid(&self) -> bool {
          true
        }
      }
    )*
  };
}

dummy_trailer!(
  (),
  u8,
  u16,
  u32,
  u64,
  u128,
  usize,
  i8,
  i16,
  i32,
  i64,
  i128,
  isize,
  core::sync::atomic::AtomicUsize,
  core::sync::atomic::AtomicIsize,
  core::sync::atomic::AtomicU8,
  core::sync::atomic::AtomicI8,
  core::sync::atomic::AtomicU16,
  core::sync::atomic::AtomicI16,
  core::sync::atomic::AtomicU32,
  core::sync::atomic::AtomicI32,
  core::sync::atomic::AtomicU64,
  core::sync::atomic::AtomicI64,
  core::sync::atomic::AtomicBool,
);

/// Time related trailers.
#[cfg(feature = "time")]
pub mod time {
  use super::Trailer;
  use ::time::OffsetDateTime;

  macro_rules! methods {
    ($ident:ident($inner:ident: $from:ident <-> $into:ident)) => {
      impl core::fmt::Display for $ident {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
          write!(
            f,
            "{}",
            OffsetDateTime::$from(self.0).expect("valid timestamp")
          )
        }
      }

      impl core::fmt::Debug for $ident {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
          write!(
            f,
            "{}",
            OffsetDateTime::$from(self.0).expect("valid timestamp")
          )
        }
      }

      impl From<$ident> for $inner {
        fn from(ts: $ident) -> Self {
          ts.0
        }
      }

      impl TryFrom<$inner> for $ident {
        type Error = time::error::ComponentRange;

        fn try_from(value: $inner) -> Result<Self, Self::Error> {
          OffsetDateTime::$from(value).map(|t| Self(t.$into()))
        }
      }
    };
  }

  macro_rules! timestamp {
    ($(
      [$($meta:meta)*]
      $ident:ident($inner:ident: $from:ident <-> $into:ident)
    ),+ $(,)?) => {
      $(
        $(
          #[$meta]
        )*
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $ident($inner);

        methods!($ident($inner: $from <-> $into));

        impl $ident {
          /// Returns the current timestamp.
          #[inline]
          pub fn now() -> Self {
            Self(OffsetDateTime::now_utc().$into())
          }
        }
      )*
    };
  }

  timestamp!(
    [doc = "A utc timestamp [`Trailer`] implementation."]
    Timestamp(i64: from_unix_timestamp <-> unix_timestamp),
    [doc = "A utc timestamp with nanoseconds [`Trailer`] implementation."]
    TimestampNanos(i128: from_unix_timestamp_nanos <-> unix_timestamp_nanos),
  );

  dummy_trailer!(Timestamp, TimestampNanos);

  macro_rules! ttl {
    ($(
      [$($meta:meta)*]
      $ident:ident($inner:ident: $from:ident <-> $into:ident)
    ),+ $(,)?) => {
      $(
        $(
          #[$meta]
        )*
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $ident($inner);

        methods!($ident($inner: $from <-> $into));

        impl $ident {
          /// Creates a new ttl.
          #[inline]
          pub fn new(ttl: std::time::Duration) -> Self {
            Self((OffsetDateTime::now_utc() + ttl).$into())
          }

          /// Returns `true` if the ttl is expired.
          #[inline]
          pub fn is_expired(&self) -> bool {
            OffsetDateTime::now_utc().$into() > self.0
          }
        }

        unsafe impl Trailer for $ident {
          #[inline]
          fn is_valid(&self) -> bool {
            !self.is_expired()
          }
        }
      )*
    };
  }

  ttl!(
    [doc = "A ttl [`Trailer`] implementation."]
    Ttl(i64: from_unix_timestamp <-> unix_timestamp),
    [doc = "A ttl with nanoseconds [`Trailer`] implementation."]
    TtlNanos(i128: from_unix_timestamp_nanos <-> unix_timestamp_nanos),
  );
}

mod sync {
  #[cfg(not(feature = "loom"))]
  pub(crate) use core::sync::atomic::*;

  #[cfg(feature = "loom")]
  pub(crate) use loom::sync::atomic::*;
}
