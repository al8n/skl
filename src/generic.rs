mod builder;
mod list;

/// Generic `SkipMap` implementation with multiple versions support.
pub mod multiple_version;

/// Generic `SkipMap` implementation without multiple versions support.
pub mod unique;

/// Iterators for the skipmaps.
pub mod iter {
  pub use super::list::iterator::{Iter, Range};
}

/// Entry references for the skipmaps.
pub mod entry {
  pub use super::list::EntryRef;
}

pub use builder::Builder;

pub use dbutils::{
  equivalent::{Comparable, Equivalent},
  equivalentor::{
    Ascend, Comparator, Descend, Equivalentor, TypeRefComparator, TypeRefEquivalentor,
    TypeRefQueryComparator, TypeRefQueryEquivalentor,
  },
  types::*,
};

use super::{Active, MaybeTombstone, State};
