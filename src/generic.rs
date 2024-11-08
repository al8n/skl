mod builder;
mod list;
mod multiple_version;
mod unique;

/// Iterators for the skipmaps.
pub mod iter {
  pub use super::list::iterator::{Iter, IterAll};
}

/// Entry references for the skipmaps.
pub mod entry {
  pub use super::list::{EntryRef, VersionedEntryRef};
}

pub use builder::*;
