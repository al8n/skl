#![doc = include_str!("../README.md")]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![deny(missing_docs)]
#![allow(clippy::type_complexity, clippy::mut_from_ref)]

extern crate alloc;

#[cfg(feature = "std")]
extern crate std;

mod error;
pub use error::Error;

mod value;
pub use value::{Value, ValueRef};
mod key;
pub use key::{Key, KeyRef};

/// Key and Value types used by [badger](https://github.com/dgraph-io/badger)
pub mod badger {
  pub use super::value::badger::*;
  pub use super::key::badger::*;
}

// mod map;
// pub use crate::map::{SkipMap, SkipMapIterator, UniSkipMapIterator};
mod map2;
pub use map2::*;

const NODE_ALIGNMENT_FACTOR: usize = core::mem::align_of::<u32>();

/// Comparator is used for users to define their own key comparison logic.
/// e.g. some key-value database developers may want to alpabetically comparation
pub trait Comparator {
  /// Compares two byte slices.
  fn compare(&self, a: &[u8], b: &[u8]) -> core::cmp::Ordering;
}

impl Comparator for () {
  #[inline]
  fn compare(&self, a: &[u8], b: &[u8]) -> core::cmp::Ordering {
    a.cmp(b)
  }
}

/// A marker trait, which gives the key-value database developers the ability to add extra information
/// to the key or value provided by the end-users. The only way to implement this trait is
///
/// **NB:**
///
/// The alignment of the type implements this trait must be a multiple of `4`,
/// typically a `u32`, `u64`, `u128` and etc.
/// This is forced to guarantee we must make sure there is no read unalignment pointer happen,
/// since read unalignment pointer will lead to UB(Undefined Behavior) on some platforms.
///
/// See [`Key`](crate::Key) for more details.
pub trait KeyTrailer: Copy + Sized + Ord {}

/// A marker trait, which gives the key-value database developers the ability to add extra information
/// to the key or value provided by the end-users. The only way to implement this trait is
///
/// **NB:**
///
/// The alignment of the type implements this trait must be a multiple of `4`,
/// typically a `u32`, `u64`, `u128` and etc.
/// This is forced to guarantee we must make sure there is no read unalignment pointer happen,
/// since read unalignment pointer will lead to UB(Undefined Behavior) on some platforms.
///
/// See [`Value`](crate::Value) for more details.
pub trait ValueTrailer: Copy + Sized {}


macro_rules! trailer {
  ($($ty:ty), +$(,)?) => {
    $(
      impl KeyTrailer for $ty {}

      impl ValueTrailer for $ty {}
    )*
  };
}

trailer!((), u32, u64, u128);

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

// #[cfg(test)]
// mod utils;
