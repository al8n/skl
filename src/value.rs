#![allow(clippy::misnamed_getters)]

use bytes::Bytes;

use super::*;

#[viewit::viewit(
  vis_all = "pub(crate)",
  setters(vis_all = "pub"),
  getters(vis_all = "pub")
)]
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct ValueRef<'a> {
  #[viewit(
    getter(const, rename = "meta", attrs(doc(hidden))),
    setter(vis = "pub(crate)", const, rename = "with_meta", attrs(doc(hidden)))
  )]
  meta: u8,
  #[viewit(getter(const), setter(const, rename = "with_user_meta"))]
  user_meta: u8,
  #[viewit(getter(const, rename = "ttl"), setter(const, rename = "with_ttl"))]
  expires_at: u64,
  #[viewit(getter(const))]
  value: &'a [u8],
  #[viewit(
    getter(const, rename = "version", attrs(doc(hidden))),
    setter(const, rename = "with_version", attrs(doc(hidden)))
  )]
  version: u64,
}

impl<'a> AsRef<[u8]> for ValueRef<'a> {
  fn as_ref(&self) -> &[u8] {
    self.value
  }
}

impl<'a> core::ops::Deref for ValueRef<'a> {
  type Target = [u8];

  fn deref(&self) -> &Self::Target {
    self.as_ref()
  }
}

impl<'a> ValueRef<'a> {
  #[inline]
  pub const fn new(src: &'a [u8]) -> Self {
    Self {
      meta: 0,
      user_meta: 0,
      expires_at: 0,
      value: src,
      version: 0,
    }
  }

  #[inline]
  pub fn into_owned(&self) -> Value {
    Value {
      meta: self.meta,
      user_meta: self.user_meta,
      expires_at: self.expires_at,
      value: Bytes::copy_from_slice(self.value),
      version: self.version,
    }
  }

  /// The size of the Value when encoded
  #[inline]
  pub const fn encoded_size(&self) -> usize {
    1 + 1 + self.value.len() + u64_varint_size(self.expires_at)
  }

  /// Uses the length of the slice to infer the length of the Value field.
  #[inline]
  pub fn decode<'b: 'a>(b: &'b [u8]) -> Self {
    let (expires_at, u64_varint_size) = uvarint(b);

    Self {
      meta: b[0],
      user_meta: b[1],
      expires_at,
      value: &b[(2 + u64_varint_size) as usize..],
      version: 0,
    }
  }

  /// Expects a slice of length at least `self.encoded_size()`.
  #[inline]
  pub fn encode(&self, dst: &mut [u8]) -> u32 {
    dst[0] = self.meta;
    dst[1] = self.user_meta;
    let u64_varint_size = put_uvarint(&mut dst[2..], self.expires_at);
    (2 + u64_varint_size + copy(self.value, &mut dst[2 + u64_varint_size..])) as u32
  }
}

#[viewit::viewit(vis_all = "", setters(vis_all = "pub"), getters(vis_all = "pub"))]
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Value {
  #[viewit(
    getter(const, rename = "meta", attrs(doc(hidden))),
    setter(vis = "pub(crate)", const, rename = "with_meta", attrs(doc(hidden)))
  )]
  meta: u8,
  #[viewit(getter(const), setter(const, rename = "with_user_meta"))]
  user_meta: u8,
  #[viewit(getter(const, rename = "ttl"), setter(const, rename = "with_ttl"))]
  expires_at: u64,
  #[viewit(getter(const, style = "ref"))]
  value: Bytes,
  #[viewit(
    getter(const, rename = "version", attrs(doc(hidden))),
    setter(const, rename = "with_version", attrs(doc(hidden)))
  )]
  version: u64,
}

impl AsRef<[u8]> for Value {
  fn as_ref(&self) -> &[u8] {
    self.value.as_ref()
  }
}

impl core::ops::Deref for Value {
  type Target = [u8];

  fn deref(&self) -> &Self::Target {
    self.as_ref()
  }
}

impl Default for Value {
  #[inline]
  fn default() -> Self {
    Self::new()
  }
}

impl Value {
  #[inline]
  pub const fn new() -> Self {
    Self {
      meta: 0,
      user_meta: 0,
      expires_at: 0,
      value: Bytes::new(),
      version: 0,
    }
  }

  #[inline]
  pub const fn from_bytes(val: Bytes) -> Self {
    Self {
      meta: 0,
      user_meta: 0,
      expires_at: 0,
      value: val,
      version: 0,
    }
  }

  #[inline]
  pub fn copy_from_slice(val: &[u8]) -> Self {
    Self {
      meta: 0,
      user_meta: 0,
      expires_at: 0,
      value: Bytes::copy_from_slice(val),
      version: 0,
    }
  }

  /// The size of the Value when encoded
  #[inline]
  pub const fn encoded_size(&self) -> usize {
    1 + 1 + self.value.len() + u64_varint_size(self.expires_at)
  }

  /// Uses the length of the slice to infer the length of the Value field.
  #[inline]
  pub fn decode(b: &[u8]) -> Self {
    let (expires_at, u64_varint_size) = uvarint(b);

    Self {
      meta: b[0],
      user_meta: b[1],
      expires_at,
      value: Bytes::copy_from_slice(&b[(2 + u64_varint_size) as usize..]),
      version: 0,
    }
  }

  /// Expects a slice of length at least `self.encoded_size()`.
  #[inline]
  pub fn encode(&self, dst: &mut [u8]) -> u32 {
    dst[0] = self.meta;
    dst[1] = self.user_meta;
    let u64_varint_size = put_uvarint(&mut dst[2..], self.expires_at);
    (2 + u64_varint_size + copy(self.value.as_ref(), &mut dst[2 + u64_varint_size..])) as u32
  }

  /// Encodes the Value into a vec.
  #[inline]
  pub fn encode_to_vec(&self) -> Vec<u8> {
    let mut vec = vec![0; self.encoded_size()];
    vec[0] = self.meta;
    vec[1] = self.user_meta;
    let u64_varint_size = put_uvarint(&mut vec[2..], self.expires_at);
    copy(&self.value, &mut vec[2 + u64_varint_size..]);
    vec
  }

  #[inline]
  pub fn into_bytes(self) -> Bytes {
    self.value
  }

  #[inline]
  pub fn as_value_ref(&self) -> ValueRef {
    ValueRef {
      meta: self.meta,
      user_meta: self.user_meta,
      expires_at: self.expires_at,
      value: self.value.as_ref(),
      version: self.version,
    }
  }

  #[inline]
  pub fn set_meta(&mut self, meta: u8) {
    self.meta = meta;
  }

  #[inline]
  pub fn set_ttl(&mut self, expires_at: u64) {
    self.expires_at = expires_at;
  }

  #[inline]
  pub fn set_user_meta(&mut self, user_meta: u8) {
    self.user_meta = user_meta;
  }

  #[inline]
  pub fn set_version(&mut self, version: u64) {
    self.version = version;
  }

  #[inline]
  pub fn set_data(&mut self, data: Bytes) {
    self.value = data;
  }
}

impl From<Bytes> for Value {
  #[inline]
  fn from(val: Bytes) -> Self {
    Self::from_bytes(val)
  }
}

impl From<Value> for Bytes {
  #[inline]
  fn from(val: Value) -> Self {
    val.value
  }
}

impl From<&Value> for Bytes {
  #[inline]
  fn from(val: &Value) -> Self {
    val.value.clone()
  }
}

impl From<&[u8]> for Value {
  #[inline]
  fn from(val: &[u8]) -> Self {
    Self::from_bytes(Bytes::copy_from_slice(val))
  }
}

impl<'a> From<&'a str> for Value {
  #[inline]
  fn from(val: &'a str) -> Self {
    Self::from_bytes(Bytes::copy_from_slice(val.as_bytes()))
  }
}

impl From<String> for Value {
  #[inline]
  fn from(val: String) -> Self {
    Self::from_bytes(Bytes::from(val))
  }
}

impl From<&String> for Value {
  #[inline]
  fn from(val: &String) -> Self {
    Self::from_bytes(Bytes::copy_from_slice(val.as_bytes()))
  }
}

impl From<Box<[u8]>> for Value {
  fn from(data: Box<[u8]>) -> Self {
    Self::from_bytes(Bytes::from(data))
  }
}

impl From<&Bytes> for Value {
  #[inline]
  fn from(val: &Bytes) -> Self {
    Self::from_bytes(val.clone())
  }
}

impl<'a> PartialEq<ValueRef<'a>> for Value {
  fn eq(&self, other: &ValueRef<'a>) -> bool {
    self.as_value_ref().eq(other)
  }
}

impl<'a> PartialEq<Value> for ValueRef<'a> {
  fn eq(&self, other: &Value) -> bool {
    self.eq(&other.as_value_ref())
  }
}

/// The maximum length of a varint-encoded N-bit integer.
const MAX_VARINT_LEN64: usize = 10;

#[inline]
const fn u64_varint_size(mut x: u64) -> usize {
  let mut n = 0;
  loop {
    n += 1;
    x >>= 7;
    if x == 0 {
      break;
    }
  }
  n
}

/// Uvarint decodes a u64 from `buf` and returns that value and the number of bytes read.
/// If an error occurred, the value is 0 and the number of bytes `n` is <= 0, where:
/// - n == 0: `buf` too small
/// - n  < 0: value larger than 64 bits (overflow) and -n is the number of bytes read.
fn uvarint(buf: &[u8]) -> (u64, isize) {
  let mut x: u64 = 0;
  let mut s: u32 = 0;
  for (i, &b) in buf.iter().enumerate() {
    if i == MAX_VARINT_LEN64 {
      // Catch byte reads past MAX_VARINT_LEN64.
      return (0, -(i as isize + 1)); // overflow
    }
    if b < 0x80 {
      if i == MAX_VARINT_LEN64 - 1 && b > 1 {
        return (0, -(i as isize + 1)); // overflow
      }
      return (x | ((b as u64) << s), i as isize + 1);
    }
    x |= ((b & 0x7f) as u64) << s;
    s += 7;
  }
  (0, 0)
}

/// Encodes a uint64 into buf and returns the number of bytes written.
///
/// # Panic
/// The buffer is too small.
#[inline]
fn put_uvarint(buf: &mut [u8], mut x: u64) -> usize {
  let mut i = 0;
  while x >= 0x80 {
    buf[i] = (x as u8) | 0x80;
    x >>= 7;
    i += 1;
  }
  buf[i] = x as u8;
  i + 1
}

/// Copies elements from a source slice into a destination slice. (As a special case, it also will copy bytes from a string to a slice of bytes.) The source and destination may overlap.
/// Copy returns the number of elements copied, which will be the minimum of `src.len()` and `dst.len()`.
#[inline]
fn copy(src: &[u8], dst: &mut [u8]) -> usize {
  let count = std::cmp::min(dst.len(), src.len());
  unsafe {
    core::ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), count);
  }
  count
}
