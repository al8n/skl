use core::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

/// A reference counter trait.
pub trait RefCounter: Clone {
  /// Creates a new reference counter.
  fn new() -> Self;

  /// Returns the current reference count.
  fn load(&self, order: Ordering) -> usize;

  /// Increments the reference count, returning the old count.
  fn fetch_add(&self, order: Ordering) -> usize;

  /// Decrements the reference count, returning the old count.
  fn fetch_sub(&self, order: Ordering) -> usize;
}

impl RefCounter for std::rc::Rc<core::cell::Cell<usize>> {
  #[inline]
  fn new() -> Self {
    std::rc::Rc::new(core::cell::Cell::new(1))
  }

  #[inline]
  fn load(&self, _: Ordering) -> usize {
    self.get()
  }

  #[inline]
  fn fetch_add(&self, _: Ordering) -> usize {
    let count = self.get();
    self.set(count + 1);
    count
  }

  #[inline]
  fn fetch_sub(&self, _: Ordering) -> usize {
    let count = self.get();
    self.set(count - 1);
    count
  }
}

impl RefCounter for Arc<AtomicUsize> {
  #[inline]
  fn new() -> Self {
    Arc::new(AtomicUsize::new(1))
  }

  #[inline]
  fn load(&self, order: Ordering) -> usize {
    AtomicUsize::load(self, order)
  }

  #[inline]
  fn fetch_add(&self, order: Ordering) -> usize {
    AtomicUsize::fetch_add(self, 1, order)
  }

  #[inline]
  fn fetch_sub(&self, order: Ordering) -> usize {
    AtomicUsize::fetch_sub(self, 1, order)
  }
}
