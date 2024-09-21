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
pub use base::{AllVersionsIter, Entry, EntryRef, Iter, VersionedEntry, VersionedEntryRef};

mod allocator;
pub use allocator::GenericAllocator;

mod error;
pub use error::Error;

/// Implementations for concurrent environments.
pub mod sync;

/// Implementations for single-threaded environments.
pub mod unsync;

mod builder;
pub use builder::*;

mod constructor;
pub use constructor::*;

mod types;
pub use types::*;

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

macro_rules! builder {
  ($($name:ident($size:ident)),+ $(,)?) => {
    $(
      paste::paste! {
        #[doc = "A " [< $name: snake>] " builder for the [`SkipList`], which requires the " [< $name: snake>] " size for accurate allocation and a closure to build the " [< $name: snake>]]
        #[derive(Copy, Clone, Debug)]
        pub struct [< $name Builder >] <F> {
          size: $size,
          f: F,
        }

        impl<F> [< $name Builder >]<F> {
          #[doc = "Creates a new `" [<$name Builder>] "` with the given size and builder closure."]
          #[inline]
          pub const fn new<E>(size: $size, f: F) -> Self
          where
            F: for<'a> FnOnce(&mut VacantBuffer<'a>) -> Result<(), E>,
          {
            Self { size, f }
          }

          #[doc = "Returns the required" [< $name: snake>] "size."]
          #[inline]
          pub const fn size(&self) -> $size {
            self.size
          }

          #[doc = "Returns the " [< $name: snake>] "builder closure."]
          #[inline]
          pub const fn builder(&self) -> &F {
            &self.f
          }

          /// Deconstructs the value builder into the size and the builder closure.
          #[inline]
          pub fn into_components(self) -> ($size, F) {
            (self.size, self.f)
          }
        }
      }
    )*
  };
}

builder!(Value(u32), Key(KeySize));

/// A trait for extra information that can be stored with entry in the skiplist.
///
/// ## Safety
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

mod common {
  #[cfg(not(feature = "loom"))]
  pub(crate) use core::sync::atomic::*;

  #[cfg(feature = "loom")]
  pub(crate) use loom::sync::atomic::*;
}
