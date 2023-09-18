use crate::ArenaError;

/// Error type for the [`SkipMap`](crate::SkipMap).
///
/// [`SkipMap`]: crate::SkipMap
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
  /// Indicates that the arena is full
  Full(ArenaError),

  /// Indicates that an entry with the specified key already
  /// exists in the skiplist. As a low-level crate, duplicate entries are not directly supported and
  /// instead must be handled by the user.
  Duplicated,

  /// Indicates that the value is too large to be stored in the [`SkipMap`](super::SkipMap).
  ValueTooLarge(u64),

  /// Indicates that the key is too large to be stored in the [`SkipMap`](super::SkipMap).
  KeyTooLarge(u64),

  /// Indicates that the entry is too large to be stored in the [`SkipMap`](super::SkipMap).
  EntryTooLarge(u64),
}

impl core::fmt::Display for Error {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match self {
      Self::Full(e) => write!(f, "{e}"),
      Self::Duplicated => write!(f, "key already exists in the skipmap"),
      Self::ValueTooLarge(size) => write!(f, "value size {} is too large", size),
      Self::KeyTooLarge(size) => write!(f, "key size {} is too large", size),
      Self::EntryTooLarge(size) => write!(f, "entry size {size} is too large",),
    }
  }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {}

impl From<ArenaError> for Error {
  fn from(e: ArenaError) -> Self {
    Self::Full(e)
  }
}
