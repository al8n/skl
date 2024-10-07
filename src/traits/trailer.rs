pub use zerocopy;

/// A trait for extra information that can be stored with entry in the skiplist. e.g. TTL information and etc.
///
/// For more details, see [`FromBytes`](zerocopy::FromBytes).
pub trait Trailer: core::fmt::Debug + zerocopy::FromBytes {
  /// Returns `true` if the trailer is valid. If a trailer is not valid, it will be ignored when
  /// read or iterated, but users can still access such entry through `get_versioned` or `iter_all_versions`.
  #[inline]
  fn is_valid(&self) -> bool {
    true
  }
}

macro_rules! dummy_trailer {
  ($($t:ty),+ $(,)?) => {
    $(
      impl Trailer for $t {
        #[inline]
        fn is_valid(&self) -> bool {
          true
        }
      }

      impl<const N: usize> Trailer for [$t; N] {
        #[inline]
        fn is_valid(&self) -> bool {
          true
        }
      }
    )*
  };
}

dummy_trailer!(
  (),
  u8,
  u16,
  u32,
  u64,
  u128,
  usize,
  i8,
  i16,
  i32,
  i64,
  i128,
  isize,
  core::sync::atomic::AtomicUsize,
  core::sync::atomic::AtomicIsize,
  core::sync::atomic::AtomicU8,
  core::sync::atomic::AtomicI8,
  core::sync::atomic::AtomicU16,
  core::sync::atomic::AtomicI16,
  core::sync::atomic::AtomicU32,
  core::sync::atomic::AtomicI32,
  core::sync::atomic::AtomicU64,
  core::sync::atomic::AtomicI64,
);

/// Time related trailers.
#[cfg(feature = "time")]
pub mod time {
  use super::Trailer;
  use ::time::OffsetDateTime;

  macro_rules! methods {
    ($ident:ident($inner:ident: $from:ident <-> $into:ident)) => {
      impl core::fmt::Display for $ident {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
          write!(
            f,
            "{}",
            OffsetDateTime::$from(self.0).expect("valid timestamp")
          )
        }
      }

      impl core::fmt::Debug for $ident {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
          write!(
            f,
            "{}",
            OffsetDateTime::$from(self.0).expect("valid timestamp")
          )
        }
      }

      impl From<$ident> for $inner {
        fn from(ts: $ident) -> Self {
          ts.0
        }
      }

      impl TryFrom<$inner> for $ident {
        type Error = time::error::ComponentRange;

        fn try_from(value: $inner) -> Result<Self, Self::Error> {
          OffsetDateTime::$from(value).map(|t| Self(t.$into()))
        }
      }
    };
  }

  macro_rules! timestamp {
    ($(
      [$($meta:meta)*]
      $ident:ident($inner:ident: $from:ident <-> $into:ident)
    ),+ $(,)?) => {
      $(
        $(
          #[$meta]
        )*
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, zerocopy::FromBytes)]
        pub struct $ident($inner);

        methods!($ident($inner: $from <-> $into));

        impl $ident {
          /// Returns the current timestamp.
          #[inline]
          pub fn now() -> Self {
            Self(OffsetDateTime::now_utc().$into())
          }
        }
      )*
    };
  }

  timestamp!(
    [doc = "A utc timestamp [`Trailer`] implementation."]
    Timestamp(i64: from_unix_timestamp <-> unix_timestamp),
    [doc = "A utc timestamp with nanoseconds [`Trailer`] implementation."]
    TimestampNanos(i128: from_unix_timestamp_nanos <-> unix_timestamp_nanos),
  );

  dummy_trailer!(Timestamp, TimestampNanos);

  macro_rules! ttl {
    ($(
      [$($meta:meta)*]
      $ident:ident($inner:ident: $from:ident <-> $into:ident)
    ),+ $(,)?) => {
      $(
        $(
          #[$meta]
        )*
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, zerocopy::FromBytes)]
        pub struct $ident($inner);

        methods!($ident($inner: $from <-> $into));

        impl $ident {
          /// Creates a new ttl.
          #[inline]
          pub fn new(ttl: std::time::Duration) -> Self {
            Self((OffsetDateTime::now_utc() + ttl).$into())
          }

          /// Returns `true` if the ttl is expired.
          #[inline]
          pub fn is_expired(&self) -> bool {
            OffsetDateTime::now_utc().$into() > self.0
          }
        }

        impl Trailer for $ident {
          #[inline]
          fn is_valid(&self) -> bool {
            !self.is_expired()
          }
        }
      )*
    };
  }

  ttl!(
    [doc = "A ttl [`Trailer`] implementation."]
    Ttl(i64: from_unix_timestamp <-> unix_timestamp),
    [doc = "A ttl with nanoseconds [`Trailer`] implementation."]
    TtlNanos(i128: from_unix_timestamp_nanos <-> unix_timestamp_nanos),
  );
}
