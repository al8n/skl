mod list;

/// Dynamic key-value `SkipMap` implementation with multiple versions support.
pub mod multiple_version;

/// Dynamic key-value `SkipMap` implementation without multiple versions support.
pub mod unique;

mod builder;
pub use builder::Builder;

/// Iterators for the skipmaps.
pub mod iter {
  pub use super::list::iterator::Iter;
}

/// Entry references for the skipmaps.
pub mod entry {
  pub use super::list::EntryRef;
}

pub use dbutils::equivalentor::{BytesComparator, BytesEquivalentor, BytesRangeComparator};

/// Ascend is a comparator that compares byte slices in ascending order.
pub type Ascend = dbutils::equivalentor::Ascend<[u8]>;

/// Ascend is a comparator that compares byte slices in ascending order.
pub type Descend = dbutils::equivalentor::Descend<[u8]>;
