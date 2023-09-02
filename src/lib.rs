//! A thread-safe skiplist implementation for writing memery table, SST table or something else.
//! skl-rs is a pure Rust implementation for https://github.com/dgraph-io/badger/tree/master/skl
//!
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
// #![deny(missing_docs)]

extern crate alloc;

#[cfg(feature = "std")]
extern crate std;

mod skl;
pub use crate::skl::{Skiplist, SkiplistIterator, UniSkiplistIterator};

mod value;
pub use value::*;
mod key;
pub use key::*;

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

#[cfg(test)]
mod utils;
