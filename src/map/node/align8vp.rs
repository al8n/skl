use crate::sync::{AtomicU64, Ordering};

#[repr(C, align(8))]
pub(crate) struct ValuePointer(AtomicU64);

impl core::fmt::Debug for ValuePointer {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    let (offset, len) = decode_value(self.0.load(Ordering::Relaxed));
    f.debug_struct("ValuePointer")
      .field("offset", &offset)
      .field("len", &len)
      .finish()
  }
}

impl ValuePointer {
  #[inline]
  pub(crate) const fn new(offset: u32, len: u32) -> Self {
    Self(AtomicU64::new(encode_value(offset, len)))
  }

  #[inline]
  pub(crate) const fn remove(offset: u32) -> Self {
    Self(AtomicU64::new(encode_value(offset, u32::MAX)))
  }

  #[inline]
  pub(crate) fn load(&self, ordering: Ordering) -> (u32, u32) {
    decode_value(self.0.load(ordering))
  }

  #[inline]
  pub(crate) fn store(&self, offset: u32, len: u32, ordering: Ordering) {
    self.0.store(encode_value(offset, len), ordering);
  }

  #[inline]
  pub(crate) fn mark_remove(&self) {
    let old = self.0.load(Ordering::Acquire);
    let (offset, _) = decode_value(old);
    let new = encode_value(offset, u32::MAX);
    let _ = self.0.compare_exchange(old, new, Ordering::SeqCst, Ordering::Relaxed);
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