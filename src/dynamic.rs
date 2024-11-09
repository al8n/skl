#![allow(single_use_lifetimes)]

mod list;

/// Dynamic key-value `SkipMap` implementation with multiple versions support.
pub mod multiple_version;

/// Dynamic key-value `SkipMap` implementation without multiple versions support.
pub mod unique;

mod builder;
pub use builder::Builder;

/// Iterators for the skipmaps.
pub mod iter {
  pub use super::list::iterator::{Iter, IterAll};
}

/// Entry references for the skipmaps.
pub mod entry {
  pub use super::list::{EntryRef, VersionedEntryRef};
}

pub use dbutils::equivalentor::*;
