use crate::ArenaError;

/// Error type for the [`SkipSet`](crate::SkipSet).
///
/// [`SkipSet`]: crate::SkipSet
#[derive(Debug)]
pub enum Error {
  /// Indicates that the arena is full
  Full(ArenaError),

  /// Indicates that the key is too large to be stored in the [`SkipSet`](crate::SkipSet).
  KeyTooLarge(u64),

  /// Indicates that the entry is too large to be stored in the [`SkipSet`](crate::SkipSet).
  EntryTooLarge(u64),

  /// Readonly skipmap
  Readonly,
}

impl core::fmt::Display for Error {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match self {
      Self::Full(e) => write!(f, "{e}"),
      Self::KeyTooLarge(size) => write!(f, "key size {} is too large", size),
      Self::EntryTooLarge(size) => write!(f, "entry size {size} is too large",),
      Self::Readonly => write!(f, "skipset is read only"),
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

#[cfg(test)]
#[test]
fn test_fmt() {
  assert_eq!(
    std::format!("{}", Error::KeyTooLarge(10)),
    "key size 10 is too large"
  );
  assert_eq!(
    std::format!("{}", Error::EntryTooLarge(10)),
    "entry size 10 is too large"
  );
  assert_eq!(
    std::format!("{}", Error::Full(ArenaError)),
    "allocation failed because arena is full",
  );
  assert_eq!(std::format!("{}", Error::Readonly), "skipset is read only");
}
