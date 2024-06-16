/// Error type for the [`SkipMap`](crate::SkipMap).
///
/// [`SkipMap`]: crate::SkipMap
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
  /// Indicates that the arena is full
  Arena(rarena_allocator::Error),

  /// Indicates that the value is too large to be stored in the [`SkipMap`](super::SkipMap).
  ValueTooLarge(u64),

  /// Indicates that the key is too large to be stored in the [`SkipMap`](super::SkipMap).
  KeyTooLarge(u64),

  /// Indicates that the entry is too large to be stored in the [`SkipMap`](super::SkipMap).
  EntryTooLarge(u64),

  /// Arena too small
  ArenaTooSmall,
}

impl core::fmt::Display for Error {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match self {
      Self::Arena(e) => write!(f, "{e}"),
      Self::ValueTooLarge(size) => write!(f, "value size {} is too large", size),
      Self::KeyTooLarge(size) => write!(f, "key size {} is too large", size),
      Self::EntryTooLarge(size) => write!(f, "entry size {size} is too large",),
      Self::ArenaTooSmall => write!(f, "ARENA capacity is too small"),
    }
  }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {}

impl From<rarena_allocator::Error> for Error {
  fn from(e: rarena_allocator::Error) -> Self {
    Self::Arena(e)
  }
}

impl Error {
  /// Returns a read only error.
  #[inline]
  pub const fn read_only() -> Self {
    Self::Arena(rarena_allocator::Error::ReadOnly)
  }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
pub(super) fn invalid_data<E: std::error::Error + Send + Sync + 'static>(e: E) -> std::io::Error {
  std::io::Error::new(std::io::ErrorKind::InvalidData, e)
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
pub(super) fn bad_magic_version() -> std::io::Error {
  std::io::Error::new(std::io::ErrorKind::InvalidData, "bad magic version")
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
pub(super) fn bad_version() -> std::io::Error {
  std::io::Error::new(std::io::ErrorKind::InvalidData, "bad version")
}

#[cfg(test)]
#[test]
fn test_fmt() {
  assert_eq!(
    std::format!("{}", Error::KeyTooLarge(10)),
    "key size 10 is too large"
  );
  assert_eq!(
    std::format!("{}", Error::ValueTooLarge(10)),
    "value size 10 is too large"
  );
  assert_eq!(
    std::format!("{}", Error::EntryTooLarge(10)),
    "entry size 10 is too large"
  );
  assert_eq!(
    std::format!(
      "{}",
      Error::Arena(rarena_allocator::Error::InsufficientSpace {
        requested: 10,
        available: 10
      })
    ),
    "Allocation failed: requested size is 10, but only 10 is available",
  );
  assert_eq!(
    std::format!("{}", Error::Arena(rarena_allocator::Error::ReadOnly)),
    "Arena is read-only"
  );
}
