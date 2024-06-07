use crate::sync::{AtomicU64, Ordering};

#[repr(C, align(8))]
pub(crate) struct AtomicValuePointer(AtomicU64);

impl core::fmt::Debug for AtomicValuePointer {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    let (offset, len) = decode_value(self.0.load(Ordering::Relaxed));
    f.debug_struct("AtomicValuePointer")
      .field("offset", &offset)
      .field("len", &len)
      .finish()
  }
}

impl AtomicValuePointer {
  #[inline]
  pub(crate) fn new(offset: u32, len: u32) -> Self {
    Self(AtomicU64::new(encode_value(offset, len)))
  }

  #[inline]
  pub(crate) fn remove(offset: u32) -> Self {
    Self(AtomicU64::new(encode_value(offset, u32::MAX)))
  }

  #[cfg(not(feature = "unaligned"))]
  #[inline]
  pub(crate) fn load(&self, ordering: Ordering) -> (u32, u32) {
    decode_value(self.0.load(ordering))
  }

  #[inline]
  pub(crate) fn swap(&self, offset: u32, len: u32) -> (u32, u32) {
    decode_value(self.0.swap(encode_value(offset, len), Ordering::AcqRel))
  }

  #[inline]
  pub(crate) fn compare_remove(
    &self,
    success: Ordering,
    failure: Ordering,
  ) -> Result<(u32, u32), (u32, u32)> {
    let old = self.0.load(Ordering::Acquire);
    let (offset, _) = decode_value(old);
    let new = encode_value(offset, u32::MAX);
    self
      .0
      .compare_exchange(old, new, success, failure)
      .map(decode_value)
      .map_err(decode_value)
  }
}

#[inline]
const fn encode_value(offset: u32, val_size: u32) -> u64 {
  (val_size as u64) << 32 | offset as u64
}

#[inline]
const fn decode_value(value: u64) -> (u32, u32) {
  let offset = value as u32;
  let val_size = (value >> 32) as u32;
  (offset, val_size)
}
