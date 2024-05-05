use crate::Arena;

use super::node::NodePtr;

/// An entry reference to the skipmap's entry.
#[derive(Debug, Copy, Clone)]
pub struct EntryRef<'a, T> {
  pub(super) key: &'a [u8],
  pub(super) trailer: T,
  pub(super) value: &'a [u8],
}

impl<'a, T> EntryRef<'a, T> {
  /// Returns the reference to the key
  #[inline]
  pub const fn key(&self) -> &[u8] {
    self.key
  }

  /// Returns the reference to the value
  #[inline]
  pub const fn value(&self) -> &[u8] {
    self.value
  }

  /// Returns the version of the entry
  #[inline]
  pub const fn trailer(&self) -> &T {
    &self.trailer
  }
}

impl<'a, T: Copy> EntryRef<'a, T> {
  pub(super) fn from_node(node: NodePtr<T>, arena: &'a Arena) -> EntryRef<'a, T> {
    unsafe {
      let node = node.as_ptr();
      EntryRef {
        key: node.get_key(arena),
        trailer: node.trailer,
        value: node.get_value(arena),
      }
    }
  }
}
