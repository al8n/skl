/// An entry reference to the skipmap's entry.
pub struct EntryRef<'a> {
  pub(super) key: &'a [u8],
  pub(super) version: u64,
  pub(super) value: &'a [u8],
}

impl<'a> EntryRef<'a> {
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
}
