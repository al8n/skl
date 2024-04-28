use super::*;

/// An entry reference to the skipmap's entry.
pub struct EntryRef<'a, C: Comparator> {
  pub(super) map: &'a SkipMap<C>,
  pub(super) nd: NodePtr,
  pub(super) key: &'a [u8],
  pub(super) version: u64,
  pub(super) value: &'a [u8],
}

impl<'a, C: Comparator> EntryRef<'a, C> {
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
  pub const fn version(&self) -> u64 {
    self.version
  }

  /// Returns the prev entry linked to this entry if any, otherwise returns `None`.
  #[inline]
  pub fn prev(&self) -> Option<EntryRef<'a, C>> {
    unsafe {
      let prev_ptr = self.map.get_prev(self.nd, 0);

      if prev_ptr.ptr == self.map.head.ptr {
        return None;
      }
      let prev_node = prev_ptr.as_ptr();

      Some(Self {
        map: self.map,
        nd: prev_ptr,
        key: prev_node.get_key(&self.map.arena),
        version: prev_node.version,
        value: prev_node.get_value(&self.map.arena),
      })
    }
  }

  /// Returns the next entry linked to this entry if any, otherwise returns `None`.
  #[inline]
  pub fn next(&self) -> Option<EntryRef<'a, C>> {
    unsafe {
      let next_ptr = self.map.get_next(self.nd, 0);

      if next_ptr.ptr == self.map.tail.ptr {
        return None;
      }
      let next_node = next_ptr.as_ptr();

      Some(Self {
        map: self.map,
        nd: next_ptr,
        key: next_node.get_key(&self.map.arena),
        version: next_node.version,
        value: next_node.get_value(&self.map.arena),
      })
    }
  }

  #[inline]
  pub(crate) const fn ptr(&self) -> NodePtr {
    self.nd
  }
}
