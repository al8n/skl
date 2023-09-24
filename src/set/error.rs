use crate::ArenaError;

/// Error type for the [`SkipSet`](crate::SkipSet).
#[derive(thiserror::Error, Debug)]
pub enum Error {
  /// Indicates that the arena is full and cannot perform any more
  /// allocations.
  #[error("{0}")]
  Full(#[from] ArenaError),
}
