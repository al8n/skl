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

/// A vacant value in the skiplist.
#[must_use = "vacant value must be filled with bytes."]
#[derive(Debug)]
pub struct VacantValue<'a> {
  buffer: VacantBuffer<'a>,
  key_offset: u32,
  key: &'a [u8],
}

impl<'a> core::ops::Deref for VacantValue<'a> {
  type Target = VacantBuffer<'a>;

  fn deref(&self) -> &Self::Target {
    &self.buffer
  }
}

impl<'a> core::ops::DerefMut for VacantValue<'a> {
  fn deref_mut(&mut self) -> &mut Self::Target {
    &mut self.buffer
  }
}

impl<'a> AsRef<[u8]> for VacantValue<'a> {
  fn as_ref(&self) -> &[u8] {
    &self.buffer
  }
}

impl<'a> AsMut<[u8]> for VacantValue<'a> {
  fn as_mut(&mut self) -> &mut [u8] {
    &mut self.buffer
  }
}

impl<'a> PartialEq<[u8]> for VacantValue<'a> {
  fn eq(&self, other: &[u8]) -> bool {
    self.buffer.eq(other)
  }
}

impl<'a> PartialEq<VacantValue<'a>> for [u8] {
  fn eq(&self, other: &VacantValue<'a>) -> bool {
    self.eq(&other.buffer)
  }
}

impl<'a> PartialEq<[u8]> for &VacantValue<'a> {
  fn eq(&self, other: &[u8]) -> bool {
    self.buffer.eq(other)
  }
}

impl<'a> PartialEq<&VacantValue<'a>> for [u8] {
  fn eq(&self, other: &&VacantValue<'a>) -> bool {
    self.eq(&other.buffer)
  }
}

impl<'a, const N: usize> PartialEq<[u8; N]> for VacantValue<'a> {
  fn eq(&self, other: &[u8; N]) -> bool {
    self.buffer.eq(other)
  }
}

impl<'a, const N: usize> PartialEq<VacantValue<'a>> for [u8; N] {
  fn eq(&self, other: &VacantValue<'a>) -> bool {
    self.as_ref().eq(&other.buffer)
  }
}

impl<'a, const N: usize> PartialEq<&VacantValue<'a>> for [u8; N] {
  fn eq(&self, other: &&VacantValue<'a>) -> bool {
    self.as_ref().eq(&other.buffer)
  }
}

impl<'a, const N: usize> PartialEq<[u8; N]> for &VacantValue<'a> {
  fn eq(&self, other: &[u8; N]) -> bool {
    self.buffer.eq(other)
  }
}

impl<'a, const N: usize> PartialEq<&mut VacantValue<'a>> for [u8; N] {
  fn eq(&self, other: &&mut VacantValue<'a>) -> bool {
    self.eq(&other.buffer)
  }
}

impl<'a, const N: usize> PartialEq<[u8; N]> for &mut VacantValue<'a> {
  fn eq(&self, other: &[u8; N]) -> bool {
    self.buffer.eq(other)
  }
}

impl<'a> VacantValue<'a> {
  #[inline]
  pub(crate) const fn new(key_offset: u32, key: &'a [u8], buffer: VacantBuffer<'a>) -> Self {
    Self {
      buffer,
      key_offset,
      key,
    }
  }

  /// Returns the offset of the key (corresponding to the value) in the underlying ARENA.
  #[inline]
  pub const fn key_offset(&self) -> u32 {
    self.key_offset
  }

  /// Returns the key of the vacant value.
  #[inline]
  pub const fn key(&self) -> &'a [u8] {
    self.key
  }
}

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
  /// Fill the remaining space with the given byte.
  pub fn fill(&mut self, byte: u8) {
    self.len = self.cap;
    self.value[self.len..].fill(byte);
  }

  /// Write bytes to the vacant value.
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

  /// Write bytes to the vacant value without bounds checking.
  ///
  /// # Panics
  /// - If a slice is larger than the remaining space.
  pub fn write_unchecked(&mut self, bytes: &[u8]) {
    let len = bytes.len();
    self.value[self.len..self.len + len].copy_from_slice(bytes);
    self.len += len;
  }

  /// Returns the capacity of the vacant value.
  #[inline]
  pub const fn capacity(&self) -> usize {
    self.cap
  }

  /// Returns the length of the vacant value.
  #[inline]
  pub const fn len(&self) -> usize {
    self.len
  }

  /// Returns `true` if the vacant value is empty.
  #[inline]
  pub const fn is_empty(&self) -> bool {
    self.len == 0
  }

  /// Returns the remaining space of the vacant value.
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
  Pointer {
    arena: &'a super::Arena,
    offset: u32,
    len: u32,
  },
  Remove(&'b [u8]),
  #[allow(dead_code)]
  RemoveVacant(VacantBuffer<'a>),
  RemovePointer {
    arena: &'a super::Arena,
    offset: u32,
    len: u32,
  },
}

impl<'a, 'b: 'a> Key<'a, 'b> {
  #[inline]
  pub(crate) fn release(&self, arena: &super::Arena) {
    match self {
      Self::Occupied(_) | Self::Remove(_) | Self::Pointer { .. } | Self::RemovePointer { .. } => {}
      Self::Vacant(key) | Self::RemoveVacant(key) => unsafe {
        arena.dealloc(key.offset, key.cap as u32);
      },
    }
  }

  #[inline]
  pub(crate) fn is_remove(&self) -> bool {
    matches!(
      self,
      Self::Remove(_) | Self::RemoveVacant(_) | Self::RemovePointer { .. }
    )
  }
}

impl<'a, 'b: 'a> AsRef<[u8]> for Key<'a, 'b> {
  #[inline]
  fn as_ref(&self) -> &[u8] {
    match self {
      Self::Occupied(key) | Self::Remove(key) => key,
      Self::Vacant(key) | Self::RemoveVacant(key) => key.as_ref(),
      Self::Pointer { arena, offset, len } | Self::RemovePointer { arena, offset, len } => unsafe {
        arena.get_bytes(*offset as usize, *len as usize)
      },
    }
  }
}
