#![doc = include_str!("../README.md")]
#![cfg_attr(not(all(feature = "std", test)), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
// #![deny(missing_docs)]

#[cfg(not(feature = "std"))]
extern crate alloc as std;

#[cfg(feature = "std")]
extern crate std;

#[cfg(not(feature = "std"))]
use std::{boxed::Box, string::String, vec, vec::Vec};

#[cfg(feature = "std")]
use std::{boxed::Box, string::String, vec, vec::Vec};

mod map;
pub use crate::map::{SkipMap, SkipMapIterator, UniSkipMapIterator};

mod value;
pub use value::*;
mod key;
pub use key::*;

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

#[cfg(test)]
mod utils;
