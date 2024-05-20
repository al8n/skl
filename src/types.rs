/// Returns when the bytes are too large to be written to the vacant buffer.
#[derive(Debug, Default, Clone, Copy)]
pub struct TooLarge {
  remaining: usize,
  write: usize,
}

impl core::fmt::Display for TooLarge {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    write!(
      f,
      "buffer does not have enough space (remaining {}, want {})",
      self.remaining, self.write
    )
  }
}

#[cfg(feature = "std")]
impl std::error::Error for TooLarge {}

/// A vacant buffer in the skiplist.
#[must_use = "vacant buffer must be filled with bytes."]
#[derive(Debug)]
pub struct VacantBuffer<'a> {
  value: &'a mut [u8],
  len: usize,
  cap: usize,
  pub(crate) offset: u32,
}

impl<'a> VacantBuffer<'a> {
  /// Write bytes to the occupied value.
  pub fn write(&mut self, bytes: &[u8]) -> Result<(), TooLarge> {
    let len = bytes.len();
    let remaining = self.cap - self.len;
    if len > remaining {
      return Err(TooLarge {
        remaining,
        write: len,
      });
    }

    self.value[self.len..self.len + len].copy_from_slice(bytes);
    self.len += len;
    Ok(())
  }

  /// Returns the capacity of the occupied value.
  #[inline]
  pub const fn capacity(&self) -> usize {
    self.cap
  }

  /// Returns the length of the occupied value.
  #[inline]
  pub const fn len(&self) -> usize {
    self.len
  }

  /// Returns `true` if the occupied value is empty.
  #[inline]
  pub const fn is_empty(&self) -> bool {
    self.len == 0
  }

  /// Returns the remaining space of the occupied value.
  #[inline]
  pub const fn remaining(&self) -> usize {
    self.cap - self.len
  }

  #[inline]
  pub(crate) fn new(cap: usize, offset: u32, value: &'a mut [u8]) -> Self {
    Self {
      value,
      len: 0,
      cap,
      offset,
    }
  }
}

impl<'a> core::ops::Deref for VacantBuffer<'a> {
  type Target = [u8];

  fn deref(&self) -> &Self::Target {
    &self.value[..self.len]
  }
}

impl<'a> core::ops::DerefMut for VacantBuffer<'a> {
  fn deref_mut(&mut self) -> &mut Self::Target {
    &mut self.value[..self.len]
  }
}

impl<'a> AsRef<[u8]> for VacantBuffer<'a> {
  fn as_ref(&self) -> &[u8] {
    &self.value[..self.len]
  }
}

impl<'a> AsMut<[u8]> for VacantBuffer<'a> {
  fn as_mut(&mut self) -> &mut [u8] {
    &mut self.value[..self.len]
  }
}

impl<'a> PartialEq<[u8]> for VacantBuffer<'a> {
  fn eq(&self, other: &[u8]) -> bool {
    self.value[..self.len].eq(other)
  }
}

impl<'a> PartialEq<VacantBuffer<'a>> for [u8] {
  fn eq(&self, other: &VacantBuffer<'a>) -> bool {
    self.eq(&other.value[..other.len])
  }
}

impl<'a> PartialEq<[u8]> for &VacantBuffer<'a> {
  fn eq(&self, other: &[u8]) -> bool {
    self.value[..self.len].eq(other)
  }
}

impl<'a> PartialEq<&VacantBuffer<'a>> for [u8] {
  fn eq(&self, other: &&VacantBuffer<'a>) -> bool {
    self.eq(&other.value[..other.len])
  }
}

impl<'a, const N: usize> PartialEq<[u8; N]> for VacantBuffer<'a> {
  fn eq(&self, other: &[u8; N]) -> bool {
    self.value[..self.len].eq(other.as_ref())
  }
}

impl<'a, const N: usize> PartialEq<VacantBuffer<'a>> for [u8; N] {
  fn eq(&self, other: &VacantBuffer<'a>) -> bool {
    self.as_ref().eq(&other.value[..other.len])
  }
}

impl<'a, const N: usize> PartialEq<&VacantBuffer<'a>> for [u8; N] {
  fn eq(&self, other: &&VacantBuffer<'a>) -> bool {
    self.as_ref().eq(&other.value[..other.len])
  }
}

impl<'a, const N: usize> PartialEq<[u8; N]> for &VacantBuffer<'a> {
  fn eq(&self, other: &[u8; N]) -> bool {
    self.value[..self.len].eq(other.as_ref())
  }
}

impl<'a, const N: usize> PartialEq<&mut VacantBuffer<'a>> for [u8; N] {
  fn eq(&self, other: &&mut VacantBuffer<'a>) -> bool {
    self.as_ref().eq(&other.value[..other.len])
  }
}

impl<'a, const N: usize> PartialEq<[u8; N]> for &mut VacantBuffer<'a> {
  fn eq(&self, other: &[u8; N]) -> bool {
    self.value[..self.len].eq(other.as_ref())
  }
}

pub(crate) enum Key<'a, 'b: 'a> {
  Occupied(&'b [u8]),
  Vacant(VacantBuffer<'a>),
}

impl<'a, 'b: 'a> Key<'a, 'b> {
  #[inline]
  pub(crate) fn on_fail(&self, arena: &crate::arena::Arena) {
    if let Self::Vacant(key) = self {
      arena.incr_discard(key.cap as u32);
    }
  }
}

impl<'a, 'b: 'a> AsRef<[u8]> for Key<'a, 'b> {
  #[inline]
  fn as_ref(&self) -> &[u8] {
    match self {
      Self::Occupied(key) => key,
      Self::Vacant(key) => key.as_ref(),
    }
  }
}
