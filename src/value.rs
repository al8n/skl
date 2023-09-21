use crate::Trailer;

/// Gives the users the ability to define their own value type, rather than just slice.
///
/// For a value-value database, the value inserted by the end-users will always be encoded to a u8 array.
/// But the value-value database developers are tend to add some extra information
/// to the value provided by the end-users.
/// e.g. ttl, version, tombstones, and etc.
///
/// This trait gives the value-value database developers the ability to add extra information
/// to the value provided by the end-users by associated type [`Trailer`](crate::Trailer).
///
/// # Example
///
/// 1. The [`InternalValue`](https://github.com/cockroachdb/pebble/blob/master/internal/base/internal.go#L171) of [cockroachdb's pebble](https://github.com/cockroachdb/pebble) can be implemented by using this trait as:
///
///     ```rust,no_run
///     #[repr(u64)]
///     enum InternalValueVind {
///       Delete,
///       Set,
///       Merge,
///       LogData,
///       // ...
///     }
///
///     #[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
///     #[repr(transparent)]
///     struct PebbleValueTrailer(u64);
///
///     impl skl::Trailer for PebbleValueTrailer {
///       fn encoded_size(&self) -> usize {
///         core::mem::size_of::<u64>()
///       }
///
///       fn encode(&self, buf: &mut [u8]) {
///         buf.copy_from_slice(&self.0.to_le_bytes());
///       }
///
///       fn decode(src: &[u8]) -> Self {
///         Self(u64::from_le_bytes(src[..core::mem::size_of::<u64>()].try_into().unwrap()))
///       }
///     }
///
///     impl PebbleValueTrailer {
///       fn make_trailer(seq_num: u64, kind: InternalValueVind) -> u64 {
///         (seq_num << 8) | (kind as u64)
///       }
///
///       fn seq_num(&self) -> u64 {
///         self.0 >> 8
///       }
///     }
///
///     struct PebbleValue {
///       user_value: Vec<u8>,
///       trailer: PebbleValueTrailer,
///     }
///
///     impl skl::Value for PebbleValue {
///       type Trailer = PebbleValueTrailer;
///       
///       fn as_bytes(&self) -> &[u8] {
///         self.user_value.as_slice()
///       }
///
///       fn trailer(&self) -> &Self::Trailer {
///         &self.trailer
///       }
///     }
///     ```
///
/// 2. The [`Value`]() of [dgraph's badger](https://github.com/dgraph-io/badger) can be implemented by using this trait as:
///   
///     ```rust,no_run
///
///     struct BadgerValue {
///       timestamp: u64,
///       data: Vec<u8>,
///     }
///   
///     impl skl::Value for BadgerValue {
///       type Trailer = u64;
///
///       fn as_bytes(&self) -> &[u8] {
///         self.data.as_slice()
///       }
///
///       fn trailer(&self) -> &Self::Trailer {
///         &self.timestamp
///       }
///     }
///     ```
pub trait Value {
  /// Extra information should be added for the value provided by end-users.
  type Trailer: Trailer;

  #[doc(hidden)]
  const _TRAILER_CHECV: () = {
    assert!(
      core::mem::align_of::<Self::Trailer>() % 4 == 0,
      "The alignment of the trailer type must be a multiple of 4"
    );
  };

  /// Returns the bytes of the value without the trailer.
  fn as_bytes(&self) -> &[u8];

  /// Returns the trailer of the value.
  fn trailer(&self) -> &Self::Trailer;
}

impl Value for Vec<u8> {
  type Trailer = ();

  #[inline]
  fn as_bytes(&self) -> &[u8] {
    self.as_slice()
  }

  #[inline]
  fn trailer(&self) -> &Self::Trailer {
    &()
  }
}

impl Value for Box<[u8]> {
  type Trailer = ();

  #[inline]
  fn as_bytes(&self) -> &[u8] {
    self.as_ref()
  }

  #[inline]
  fn trailer(&self) -> &Self::Trailer {
    &()
  }
}

impl Value for ::alloc::sync::Arc<[u8]> {
  type Trailer = ();

  #[inline]
  fn as_bytes(&self) -> &[u8] {
    self.as_ref()
  }

  #[inline]
  fn trailer(&self) -> &Self::Trailer {
    &()
  }
}

impl<const N: usize> Value for [u8; N] {
  type Trailer = ();

  #[inline]
  fn as_bytes(&self) -> &[u8] {
    self.as_ref()
  }

  #[inline]
  fn trailer(&self) -> &Self::Trailer {
    &()
  }
}

impl<'a> Value for &'a [u8] {
  type Trailer = ();

  #[inline]
  fn as_bytes(&self) -> &[u8] {
    self
  }

  #[inline]
  fn trailer(&self) -> &Self::Trailer {
    &()
  }
}

impl<'a> Value for &'a str {
  type Trailer = ();

  #[inline]
  fn as_bytes(&self) -> &[u8] {
    str::as_bytes(self)
  }

  #[inline]
  fn trailer(&self) -> &Self::Trailer {
    &()
  }
}

impl Value for String {
  type Trailer = ();

  #[inline]
  fn as_bytes(&self) -> &[u8] {
    self.as_bytes()
  }

  #[inline]
  fn trailer(&self) -> &Self::Trailer {
    &()
  }
}

#[cfg(feature = "bytes")]
impl Value for bytes::Bytes {
  type Trailer = ();

  #[inline]
  fn as_bytes(&self) -> &[u8] {
    self.as_ref()
  }

  #[inline]
  fn trailer(&self) -> &Self::Trailer {
    &()
  }
}

#[cfg(feature = "smallvec")]
impl<A: smallvec::Array<Item = u8>> Value for smallvec::SmallVec<A> {
  type Trailer = ();

  #[inline]
  fn as_bytes(&self) -> &[u8] {
    self.as_slice()
  }

  #[inline]
  fn trailer(&self) -> &Self::Trailer {
    &()
  }
}

#[cfg(feature = "smol_str")]
impl Value for smol_str::SmolStr {
  type Trailer = ();

  #[inline]
  fn as_bytes(&self) -> &[u8] {
    str::as_bytes(self.as_str())
  }

  #[inline]
  fn trailer(&self) -> &Self::Trailer {
    &()
  }
}

/// The value reference
pub struct ValueRef<'a, V: Value> {
  data: &'a [u8],
  trailer: V::Trailer,
}

impl<'a, V: Value> ValueRef<'a, V> {
  /// Creates a new value reference directly from the given bytes and trailer.
  #[inline]
  pub const fn new(data: &'a [u8], trailer: V::Trailer) -> Self {
    Self { data, trailer }
  }

  /// Returns the bytes of the value without the trailer.
  #[inline]
  pub const fn as_bytes(&self) -> &[u8] {
    self.data
  }

  /// Returns the trailer of the value.
  #[inline]
  pub const fn trailer(&self) -> &V::Trailer {
    &self.trailer
  }

  /// Returns the encoded size of the value.
  #[inline]
  pub fn encoded_size(&self) -> usize {
    self.data.len()
  }

  /// Encodes the value into the given buffer. The buffer must be at least `self.encoded_size()` bytes.
  pub fn encode(&self, buf: &mut [u8]) {
    let value = self.as_bytes();
    let value_len = value.len();
    buf[..value_len].copy_from_slice(value);
  }
}

/// A trait for types that can be converted to a value reference. [`ValueRef`](crate::ValueRef) is the value used to insert to the skiplist.
pub trait AsValueRef {
  /// The value type.
  type Value: Value;

  /// Converts the given value to a value reference.
  fn as_value_ref(&self) -> ValueRef<Self::Value>;
}

impl<V: Value> AsValueRef for V {
  type Value = V;

  #[inline]
  fn as_value_ref(&self) -> ValueRef<V> {
    ValueRef {
      data: self.as_bytes(),
      trailer: *self.trailer(),
    }
  }
}
