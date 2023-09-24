use crate::ArenaError;

/// Error type for the [`SkipMap`](crate::SkipMap).
///
/// [`SkipMap`]: crate::SkipMap
#[derive(thiserror::Error, Debug)]
pub enum Error {
  /// Indicates that the arena is full and cannot perform any more
  /// allocations.
  #[error("{0}")]
  Full(#[from] ArenaError),

  /// Indicates that an entry with the specified key already
  /// exists in the skiplist. As a low-level crate, duplicate entries are not directly supported and
  /// instead must be handled by the user.
  #[error("key already exists in the skiplist")]
  Duplicated,
}
