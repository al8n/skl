use super::Height;
pub use rarena_allocator::Error as ArenaError;

/// Error type for the `SkipMap`s.
#[derive(Debug)]
pub enum Error {
  /// Indicates that the arena is full
  Arena(ArenaError),

  /// Indicates that the value is too large to be stored in the `SkipMap`.
  ValueTooLarge {
    /// The size of the value.
    size: usize,
    /// The max size of the value.
    maximum_size: usize,
  },

  /// Indicates that the key is too large to be stored in the `SkipMap`.
  KeyTooLarge {
    /// The size of the key.
    size: usize,
    /// The max size of the key.
    maximum_size: usize,
  },

  /// Indicates that the entry is too large to be stored in the `SkipMap`.
  EntryTooLarge {
    /// The size of the entry.
    size: u64,
    /// The max size of the entry.
    maximum_size: u64,
  },

  /// Indicates that the height of the `SkipMap` is too large.
  InvalidHeight {
    /// The height of the `SkipMap`.
    height: Height,

    /// The max height of the `SkipMap`.
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
      Self::ValueTooLarge { size, maximum_size } => write!(
        f,
        "value size {size} larger than the maximum size {maximum_size}"
      ),
      Self::KeyTooLarge { size, maximum_size } => write!(
        f,
        "key size {size} larger than the maximum size {maximum_size}"
      ),
      Self::EntryTooLarge { size, maximum_size } => write!(
        f,
        "entry size {size} larger than the maximum size {maximum_size}",
      ),
      Self::ArenaTooSmall => write!(f, "ARENA capacity is too small"),
      Self::InvalidHeight { height, max_height } => {
        if height.to_u8() == 0 {
          write!(f, "height must be greater than 0")
        } else {
          write!(
            f,
            "height {height} is larger than the max height {max_height}"
          )
        }
      }
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      Self::IO(e) => write!(f, "{e}"),
    }
  }
}

impl core::error::Error for Error {}

impl From<ArenaError> for Error {
  fn from(e: ArenaError) -> Self {
    Self::Arena(e)
  }
}

impl Error {
  /// Returns a read only error.
  #[inline]
  pub const fn read_only() -> Self {
    Self::Arena(ArenaError::ReadOnly)
  }

  #[inline]
  pub(crate) const fn invalid_height(height: Height, max_height: Height) -> Self {
    Self::InvalidHeight { height, max_height }
  }

  #[inline]
  pub(crate) const fn invalid_key_size(key_size: usize, max_size: usize) -> Self {
    Self::KeyTooLarge {
      size: key_size,
      maximum_size: max_size,
    }
  }

  #[inline]
  pub(crate) const fn invalid_value_size(value_size: usize, max_size: usize) -> Self {
    Self::ValueTooLarge {
      size: value_size,
      maximum_size: max_size,
    }
  }

  #[inline]
  pub(crate) const fn invalid_entry_size(entry_size: u64, max_size: u64) -> Self {
    Self::EntryTooLarge {
      size: entry_size,
      maximum_size: max_size,
    }
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
