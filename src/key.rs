use super::*;
use bytes::Bytes;

pub(crate) const TIMESTAMP_SIZE: usize = core::mem::size_of::<u64>();

#[viewit::viewit(
  vis_all = "pub(crate)",
  setters(vis_all = "pub"),
  getters(vis_all = "pub")
)]
#[derive(Debug, Copy, Clone)]
pub struct KeyRef<'a> {
  #[viewit(
    getter(const, rename = "version"),
    setter(const, rename = "with_version")
  )]
  version: u64,
  #[viewit(getter(const), setter(skip))]
  data: &'a [u8],
}

impl<'a> AsRef<[u8]> for KeyRef<'a> {
  fn as_ref(&self) -> &[u8] {
    self.data
  }
}

impl<'a> core::ops::Deref for KeyRef<'a> {
  type Target = [u8];

  fn deref(&self) -> &Self::Target {
    self.as_ref()
  }
}

impl<'a> KeyRef<'a> {
  #[inline]
  pub const fn new(src: &'a [u8]) -> Self {
    Self {
      version: 0,
      data: src,
    }
  }

  #[inline]
  pub fn into_owned(&self) -> Key {
    Key {
      version: self.version,
      data: Bytes::copy_from_slice(self.data),
    }
  }
}

impl<'a> PartialEq for KeyRef<'a> {
  fn eq(&self, other: &Self) -> bool {
    self.data == other.data && self.version == other.version
  }
}

impl<'a> Eq for KeyRef<'a> {}

impl<'a> PartialOrd for KeyRef<'a> {
  fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
    Some(self.cmp(other))
  }
}

impl<'a> Ord for KeyRef<'a> {
  fn cmp(&self, other: &Self) -> core::cmp::Ordering {
    self
      .data
      .cmp(other.data)
      .then_with(|| self.version.cmp(&other.version))
  }
}

impl<'a> From<&'a [u8]> for KeyRef<'a> {
  fn from(data: &'a [u8]) -> Self {
    Self { data, version: 0 }
  }
}

impl<'a> From<&'a str> for KeyRef<'a> {
  fn from(data: &'a str) -> Self {
    Self {
      data: data.as_bytes(),
      version: 0,
    }
  }
}

#[viewit::viewit(vis_all = "", setters(vis_all = "pub"), getters(vis_all = "pub"))]
#[derive(Debug, Clone)]
pub struct Key {
  #[viewit(
    getter(const, rename = "version"),
    setter(const, rename = "with_version")
  )]
  version: u64,
  #[viewit(getter(const, style = "ref"), setter(skip))]
  data: Bytes,
}

impl AsRef<[u8]> for Key {
  fn as_ref(&self) -> &[u8] {
    self.data.as_ref()
  }
}

impl core::ops::Deref for Key {
  type Target = [u8];

  fn deref(&self) -> &Self::Target {
    self.as_ref()
  }
}

impl PartialEq for Key {
  fn eq(&self, other: &Self) -> bool {
    self.data == other.data && self.version == other.version
  }
}

impl Eq for Key {}

impl core::hash::Hash for Key {
  fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
    self.data.hash(state);
  }
}

impl PartialOrd for Key {
  fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
    Some(self.cmp(other))
  }
}

impl Ord for Key {
  fn cmp(&self, other: &Self) -> core::cmp::Ordering {
    self
      .data
      .cmp(&other.data)
      .then_with(|| self.version.cmp(&other.version))
  }
}

impl Default for Key {
  fn default() -> Self {
    Self::new()
  }
}

impl Key {
  #[inline]
  pub const fn new() -> Self {
    Self {
      data: Bytes::new(),
      version: 0,
    }
  }

  #[inline]
  pub const fn from_bytes(b: Bytes) -> Self {
    Self {
      data: b,
      version: 0,
    }
  }

  #[inline]
  pub fn as_key_ref(&self) -> KeyRef {
    KeyRef {
      version: self.version,
      data: self.data.as_ref(),
    }
  }

  /// Destruct the key, returns key and ttl of the key.
  #[inline]
  pub fn into_components(self) -> (Bytes, u64) {
    (self.data, self.version)
  }

  #[inline]
  pub fn set_ttl(&mut self, ttl: u64) {
    self.version = ttl;
  }

  /// Returns a key, with the current timestamp (in milliseconds)
  #[cfg(feature = "std")]
  #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
  pub fn with_now(src: Bytes) -> Self {
    Self {
      data: src,
      version: std::time::SystemTime::UNIX_EPOCH
        .elapsed()
        .unwrap()
        .as_millis() as u64,
    }
  }
}

impl From<Bytes> for Key {
  fn from(data: Bytes) -> Self {
    Self { data, version: 0 }
  }
}

impl<'a> From<&'a [u8]> for Key {
  fn from(data: &'a [u8]) -> Self {
    Self {
      data: Bytes::copy_from_slice(data),
      version: 0,
    }
  }
}

impl<'a> From<&'a str> for Key {
  fn from(data: &str) -> Self {
    Self {
      data: Bytes::copy_from_slice(data.as_bytes()),
      version: 0,
    }
  }
}

impl From<String> for Key {
  fn from(data: String) -> Self {
    Self {
      data: data.into(),
      version: 0,
    }
  }
}

impl From<&Key> for Key {
  fn from(key: &Key) -> Self {
    Self {
      data: key.data.clone(),
      version: key.version,
    }
  }
}

impl From<Key> for Bytes {
  fn from(key: Key) -> Self {
    key.data
  }
}

impl From<&Key> for Bytes {
  fn from(key: &Key) -> Self {
    key.data.clone()
  }
}

impl From<Vec<u8>> for Key {
  fn from(data: Vec<u8>) -> Self {
    Self {
      data: data.into(),
      version: 0,
    }
  }
}

impl From<Box<[u8]>> for Key {
  fn from(data: Box<[u8]>) -> Self {
    Self {
      data: data.into(),
      version: 0,
    }
  }
}

impl From<&Bytes> for Key {
  fn from(data: &Bytes) -> Self {
    Self {
      data: data.clone(),
      version: 0,
    }
  }
}

impl<'a> PartialEq<KeyRef<'a>> for Key {
  fn eq(&self, other: &KeyRef<'a>) -> bool {
    self.data == other.data && self.version == other.version
  }
}

impl<'a> PartialEq<Key> for KeyRef<'a> {
  fn eq(&self, other: &Key) -> bool {
    self.data == other.data && self.version == other.version
  }
}

impl<'a> PartialOrd<KeyRef<'a>> for Key {
  fn partial_cmp(&self, other: &KeyRef<'a>) -> Option<core::cmp::Ordering> {
    Some(
      self
        .data
        .as_ref()
        .cmp(other.data)
        .then_with(|| self.version.cmp(&other.version)),
    )
  }
}

impl<'a> PartialOrd<Key> for KeyRef<'a> {
  fn partial_cmp(&self, other: &Key) -> Option<core::cmp::Ordering> {
    Some(
      self
        .data
        .cmp(&other.data)
        .then_with(|| self.version.cmp(&other.version)),
    )
  }
}
