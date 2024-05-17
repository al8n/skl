use super::Ordering;
use atomic::Atomic;

#[derive(bytemuck::NoUninit, Copy, Clone, Debug)]
#[repr(C, align(4))]
struct Inner {
  offset: u32,
  len: u32,
}

#[derive(Debug)]
#[repr(C, align(4))]
pub(crate) struct ValuePointer(Atomic<Inner>);

impl ValuePointer {
  #[inline]
  pub(crate) const fn new(offset: u32, len: u32) -> Self {
    Self(Atomic::new(Inner { offset, len }))
  }

  #[inline]
  pub(crate) const fn remove(offset: u32) -> Self {
    Self(Atomic::new(Inner {
      offset,
      len: u32::MAX,
    }))
  }

  #[inline]
  pub(crate) fn load(&self, ordering: Ordering) -> (u32, u32) {
    let inner = self.0.load(ordering);
    (inner.offset, inner.len)
  }

  #[inline]
  pub(crate) fn store(&self, offset: u32, len: u32, ordering: Ordering) {
    self.0.store(Inner { offset, len }, ordering);
  }

  #[inline]
  pub(crate) fn mark_remove(&self) {
    let inner = self.0.load(Ordering::Acquire);
    let new_inner = Inner {
      offset: inner.offset,
      len: u32::MAX,
    };
    let _ = self
      .0
      .compare_exchange(inner, new_inner, Ordering::SeqCst, Ordering::Relaxed);
  }
}
