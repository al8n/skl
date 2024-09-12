use super::Height;

/// Error type for the [`SkipMap`](crate::SkipMap).
///
/// [`SkipMap`]: crate::SkipMap
#[derive(Debug)]
pub enum Error {
  /// Indicates that the arena is full
  Arena(rarena_allocator::Error),

  /// Indicates that the value is too large to be stored in the [`SkipMap`](super::SkipMap).
  ValueTooLarge(u64),

  /// Indicates that the key is too large to be stored in the [`SkipMap`](super::SkipMap).
  KeyTooLarge(u64),

  /// Indicates that the entry is too large to be stored in the [`SkipMap`](super::SkipMap).
  EntryTooLarge(u64),

  /// Indicates that the height of the [`SkipMap`](super::SkipMap) is too large.
  InvalidHeight {
    /// The height of the [`SkipMap`](super::SkipMap).
    height: Height,

    /// The max height of the [`SkipMap`](super::SkipMap).
    max_height: Height,
  },

  /// Arena too small
  ArenaTooSmall,

  /// I/O error
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  IO(std::io::Error),
}

impl core::fmt::Display for Error {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match self {
      Self::Arena(e) => write!(f, "{e}"),
      Self::ValueTooLarge(size) => write!(f, "value size {} is too large", size),
      Self::KeyTooLarge(size) => write!(f, "key size {} is too large", size),
      Self::EntryTooLarge(size) => write!(f, "entry size {size} is too large",),
      Self::ArenaTooSmall => write!(f, "ARENA capacity is too small"),
      Self::InvalidHeight { height, max_height } => write!(
        f,
        "given height {height} is larger than the max height {max_height} or less than 1"
      ),
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      Self::IO(e) => write!(f, "{e}"),
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

  #[inline]
  pub(crate) const fn invalid_height(height: Height, max_height: Height) -> Self {
    Self::InvalidHeight { height, max_height }
  }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
impl From<std::io::Error> for Error {
  fn from(e: std::io::Error) -> Self {
    Self::IO(e)
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
