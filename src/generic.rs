mod builder;
mod list;

/// Generic `SkipMap` implementation with multiple versions support.
pub mod multiple_version;

/// Generic `SkipMap` implementation without multiple versions support.
pub mod unique;

/// Iterators for the skipmaps.
pub mod iter {
  pub use super::list::iterator::{Iter, IterAll};
}

/// Entry references for the skipmaps.
pub mod entry {
  pub use super::list::{EntryRef, VersionedEntryRef};
}

pub use builder::Builder;
