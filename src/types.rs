use core::ops::{Add, AddAssign, Sub, SubAssign};

use arbitrary_int::{u27, u5, Number, TryNewError};
pub use dbutils::buffer::*;

const MAX_U5: u8 = (1 << 5) - 1;
const MAX_U27: u32 = (1 << 27) - 1;

/// Version, used for MVCC purpose, it is a 56-bit unsigned integer.
pub type Version = u64;

/// The information of the `SkipMap`, which can be used to reconstruct the `SkipMap`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Header {
  meta_offset: u32,
  head_node_offset: u32,
  tail_node_offset: u32,
}

impl Header {
  /// Returns a new `Meta` with the given meta, head node, and tail node offsets.
  #[inline]
  pub const fn new(meta_offset: u32, head_node_offset: u32, tail_node_offset: u32) -> Self {
    Self {
      meta_offset,
      head_node_offset,
      tail_node_offset,
    }
  }

  /// Returns the meta offset of the `SkipMap`.
  #[inline]
  pub const fn meta_offset(&self) -> u32 {
    self.meta_offset
  }

  /// Returns the head node offset of the `SkipMap`.
  #[inline]
  pub const fn head_node_offset(&self) -> u32 {
    self.head_node_offset
  }

  /// Returns the tail node offset of the `SkipMap`.
  #[inline]
  pub const fn tail_node_offset(&self) -> u32 {
    self.tail_node_offset
  }
}

pub(crate) mod internal {
  use core::{ptr::NonNull, sync::atomic::Ordering};

  use crate::ref_counter::RefCounter;

  /// A pointer to a value in the `SkipMap`.
  #[derive(Debug)]
  pub struct ValuePointer {
    pub(crate) value_offset: u32,
    pub(crate) value_len: u32,
  }

  impl Clone for ValuePointer {
    fn clone(&self) -> Self {
      *self
    }
  }

  impl Copy for ValuePointer {}

  impl ValuePointer {
    #[inline]
    pub(crate) const fn new(value_offset: u32, value_len: u32) -> Self {
      Self {
        value_offset,
        value_len,
      }
    }
  }

  bitflags::bitflags! {
    #[derive(Debug, Copy, Clone, Eq, PartialEq)]
    pub struct Flags: u8 {
      /// Indicates that the wal is muliple version.
      const MULTIPLE_VERSION = 0b0000_0001;
    }
  }

  /// A reference counter for [`Meta`](crate::allocator::Meta).
  #[doc(hidden)]
  pub(crate) struct RefMeta<M, R: RefCounter> {
    unify: bool,
    meta: NonNull<M>,
    ref_counter: R,
  }

  impl<M: core::fmt::Debug, R: RefCounter> core::fmt::Debug for RefMeta<M, R> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
      f.debug_struct("RefMeta")
        .field("meta", unsafe { &*self.meta.as_ptr() })
        .field("refs", &self.ref_counter.load(Ordering::Acquire))
        .field("unify", &self.unify)
        .finish()
    }
  }

  impl<M, R: RefCounter> core::ops::Deref for RefMeta<M, R> {
    type Target = M;

    #[inline]
    fn deref(&self) -> &Self::Target {
      unsafe { self.meta.as_ref() }
    }
  }

  impl<M, R: RefCounter> core::ops::DerefMut for RefMeta<M, R> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
      unsafe { self.meta.as_mut() }
    }
  }

  impl<M, R> RefMeta<M, R>
  where
    R: RefCounter,
  {
    #[inline]
    pub(crate) fn new(meta: NonNull<M>, unify: bool) -> Self {
      Self {
        meta,
        ref_counter: R::new(),
        unify,
      }
    }

    #[inline]
    pub(crate) fn refs(&self) -> usize {
      self.ref_counter.load(Ordering::Acquire)
    }
  }

  impl<M, R: RefCounter> Clone for RefMeta<M, R> {
    #[inline]
    fn clone(&self) -> Self {
      let old_size = self.ref_counter.fetch_add(Ordering::Release);
      if old_size > usize::MAX >> 1 {
        dbutils::utils::abort();
      }

      // Safety:
      // The ptr is always non-null, and the data is only deallocated when the
      // last Arena is dropped.
      Self {
        meta: self.meta,
        ref_counter: self.ref_counter.clone(),
        unify: self.unify,
      }
    }
  }

  impl<M, R: RefCounter> Drop for RefMeta<M, R> {
    fn drop(&mut self) {
      if self.ref_counter.fetch_sub(Ordering::Release) != 1 {
        return;
      }

      if self.unify {
        return;
      }

      unsafe {
        // This fence is needed to prevent reordering of use of the data and
        // deletion of the data.  Because it is marked `Release`, the decreasing
        // of the reference count synchronizes with this `Acquire` fence. This
        // means that use of the data happens before decreasing the reference
        // count, which happens before this fence, which happens before the
        // deletion of the data.
        //
        // As explained in the [Boost documentation][1],
        //
        // > It is important to enforce any possible access to the object in one
        // > thread (through an existing reference) to *happen before* deleting
        // > the object in a different thread. This is achieved by a "release"
        // > operation after dropping a reference (any access to the object
        // > through this reference must obviously happened before), and an
        // > "acquire" operation before deleting the object.
        //
        // [1]: (www.boost.org/doc/libs/1_55_0/doc/html/atomic/usage_examples.html)
        //
        // Thread sanitizer does not support atomic fences. Use an atomic load
        // instead.
        self.ref_counter.load(Ordering::Acquire);
        // Drop the data
        let _ = std::boxed::Box::from_raw(self.meta.as_ptr());
      }
    }
  }
}

macro_rules! impl_eq_and_ord {
  ($name:ident($inner:ident < $upper:ident) -> [$($target:ident),+ $(,)?]) => {
    $(
      paste::paste! {
        impl PartialEq<$target> for $name {
          #[inline]
          fn eq(&self, other: &$target) -> bool {
            let val: $upper = self.0.into();
            val.eq(&(*other as $upper))
          }
        }

        impl PartialOrd<$target> for $name {
          #[inline]
          fn partial_cmp(&self, other: &$target) -> Option<core::cmp::Ordering> {
            let val: $upper = self.0.into();
            val.partial_cmp(&(*other as $upper))
          }
        }
      }
    )*
  };
}

macro_rules! impl_signed_eq_and_ord {
  ($name:ident($inner:ident < $upper:ident) -> [$($target:ident),+ $(,)?]) => {
    $(
      paste::paste! {
        impl PartialEq<$target> for $name {
          #[inline]
          fn eq(&self, other: &$target) -> bool {
            let val: $upper = self.0.into();
            (val as i64).eq(&(*other as i64))
          }
        }

        impl PartialOrd<$target> for $name {
          #[inline]
          fn partial_cmp(&self, other: &$target) -> Option<core::cmp::Ordering> {
            let val: $upper = self.0.into();
            (val as i64).partial_cmp(&(*other as i64))
          }
        }

        impl PartialEq<$name> for $target {
          #[inline]
          fn eq(&self, other: &$name) -> bool {
            let val: $upper = other.0.into();
            (*self as i64).eq(&(val as i64))
          }
        }

        impl PartialOrd<$name> for $target {
          #[inline]
          fn partial_cmp(&self, other: &$name) -> Option<core::cmp::Ordering> {
            let val: $upper = other.0.into();
            (*self as i64).partial_cmp(&(val as i64))
          }
        }
      }
    )*
  };
}

macro_rules! impl_ops_for_ux_wrapper {
  ($name:ident($inner:ident < $upper:ident) -> [$($target:ident),+ $(,)?]) => {
    $(
      paste::paste! {
        impl Add<$target> for $name {
          type Output = Self;

          fn add(self, rhs: $target) -> Self::Output {
            let res = rhs as $upper + $upper::from(self.0);

            if res > [<MAX_ $inner:upper>] {
              panic!("attempt to add with overflow");
            }

            Self($inner::new(res))
          }
        }

        impl AddAssign<$target> for $name {
          fn add_assign(&mut self, rhs: $target) {
            let res = rhs as $upper + $upper::from(self.0);

            if res > [<MAX_ $inner:upper>] {
              panic!("attempt to add with overflow");
            }

            self.0 = $inner::new(res);
          }
        }

        impl Sub<$target> for $name {
          type Output = Self;

          fn sub(self, rhs: $target) -> Self::Output {
            let res = rhs as $upper - $upper::from(self.0);

            if res > [<MAX_ $inner:upper>] {
              panic!("attempt to substract with overflow");
            }

            Self($inner::new(res))
          }
        }

        impl SubAssign<$target> for $name {
          fn sub_assign(&mut self, rhs: $target) {
            let res = rhs as $upper - $upper::from(self.0);

            if res > [<MAX_ $inner:upper>] {
              panic!("attempt to substract with overflow");
            }

            self.0 = $inner::new(res);
          }
        }
      }
    )*
  };
}

macro_rules! impl_try_from_for_ux_wrapper {
  ($name:ident($inner:ident < $upper:ident) -> [$($target:ident),+ $(,)?]) => {
    $(
      paste::paste! {
        impl TryFrom<$target> for $name {
          type Error = TryNewError;

          #[inline]
          fn try_from(value: $target) -> Result<Self, Self::Error> {
            $inner::try_new(value as $upper).map(Self)
          }
        }

        impl $name {
          #[doc = "Try to create a" $name " from the given `" $target "`"]
          #[inline]
          pub fn [< try_from_ $target >](val: $target) -> Result<Self, TryNewError> {
            $inner::try_new(val as $upper).map(Self)
          }

          #[doc = " Creates a new " $name " from the given `" $target "`."]
          ///
          /// # Panics
          #[doc = "- If the given value is greater than `" $inner "::MAX`."]
          #[inline]
          pub const fn [< from_ $target _unchecked>](val: $target) -> Self {
            Self($inner::new(val as $upper))
          }
        }
      }
    )*
  };
}

macro_rules! impl_from_for_ux_wrapper {
  ($name:ident($inner:ident < $upper:ident) -> [$($target:ident),+ $(,)?]) => {
    $(
      paste::paste! {
        impl From<$target> for $name {
          #[inline]
          fn from(version: $target) -> Self {
            Self($inner::from(version))
          }
        }

        impl $name {
          #[doc = "Creates a new " $name " from the given `" $target "`."]
          #[inline]
          pub const fn [< from_ $target>](version: $target) -> Self {
            Self($inner::new(version as $upper))
          }
        }
      }
    )*
  };
}

macro_rules! impl_into_for_ux_wrapper {
  ($name:ident($inner:ident < $upper:ident) -> [$($target:ident),+ $(,)?]) => {
    $(
      paste::paste! {
        impl From<$name> for $target {
          #[inline]
          fn from(version: $name) -> Self {
            version.[< to_ $target>]()
          }
        }

        impl $name {
          #[doc = "Converts the " $name " to a `" $target "`."]
          #[inline]
          pub fn [< to_ $target>](&self) -> $target {
            let val: $upper = self.0.into();
            val as $target
          }
        }
      }
    )*
  };
}

macro_rules! ux_wrapper {
  (
    $(
      $([$meta:meta])*
      $name:ident($inner:ident < $upper:ident) {
        min: $min:expr,
        default: $default:expr,
        $(bits: $bits:expr,)?
        $(ord: [$($ord_target:ident),* $(,)?],)?
        $(signed_ord: [$($signed_ord_target:ident),* $(,)?],)?
        $(ops: [$($ops_target:ident),* $(,)?],)?
        $(try_from: [$($try_from_target:ident),* $(,)?],)?
        $(from: [$($from_target:ident),* $(,)?],)?
        $(into: [$($into_target:ident),* $(,)?],)?
      }
    ),+ $(,)?
  ) => {
    $(
      $(#[$meta])*
      #[derive(
        Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash,
      )]
      pub struct $name($inner);

      impl core::fmt::Display for $name {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
          write!(f, "{}", self.0)
        }
      }

      paste::paste! {
        impl $name {
          #[doc = "The maximum value of the " $name "."]
          pub const MAX: Self = Self($inner::MAX);

          #[doc = "The minimum value of the " $name "."]
          pub const MIN: Self = Self($inner::new($min));

          #[doc = "Creates a new " $name " with the default value."]
          #[inline]
          pub const fn new() -> Self {
            Self($inner::new($default))
          }

          #[doc = "Creates a new " $name " with the given value."]
          #[doc = ""]
          #[doc = "## Panics"]
          #[doc = "If the given value is greater than `" $inner "::MAX`."]
          #[inline]
          pub const fn with(val: $upper) -> Self {
            Self($inner::new(val))
          }

          /// Checked integer addition. Computes `self + rhs`, returning `None` if overflow occurred.
          #[inline]
          pub fn checked_add(self, rhs: Self) -> Option<Self> {
            self.0.checked_add(rhs.0).map(Self)
          }

          /// Checked integer subtraction. Computes `self - rhs`, returning `None` if overflow occurred.
          #[inline]
          pub fn checked_sub(self, rhs: Self) -> Option<Self> {
            self.0.checked_sub(rhs.0).and_then(|val| {
              if val < $inner::new($min) {
                None
              } else {
                Some(Self(val))
              }
            })
          }

          /// Wrapping (modular) addition. Computes `self + rhs`, wrapping around at the boundary of the type.
          #[inline]
          pub fn wrapping_add(self, rhs: Self) -> Self {
            Self(self.0.wrapping_add(rhs.0).max($inner::new($min)))
          }

          /// Wrapping (modular) subtraction. Computes `self - rhs`, wrapping around at the boundary of the type.
          #[inline]
          pub fn wrapping_sub(self, rhs: Self) -> Self {
            let val = self.0.wrapping_sub(rhs.0);
            if val < $inner::MIN {
              Self::MAX
            } else {
              Self(val)
            }
          }

          $(
            /// Create a native endian integer value from its representation as a byte array in big endian.
            #[inline]
            pub const fn from_be_bytes(bytes: [u8; { $bits >> 3 }]) -> Self {
              Self(UInt::<$upper, $bits>::from_be_bytes(bytes))
            }

            /// Create a native endian integer value from its representation as a byte array in little endian.
            #[inline]
            pub const fn from_le_bytes(bytes: [u8; { $bits >> 3 }]) -> Self {
              Self(UInt::<$upper, $bits>::from_le_bytes(bytes))
            }

            /// Returns the native endian representation of the integer as a byte array in big endian.
            #[inline]
            pub const fn to_be_bytes(self) -> [u8; { $bits >> 3 }] {
              self.0.to_be_bytes()
            }

            /// Returns the native endian representation of the integer as a byte array in little endian.
            #[inline]
            pub const fn to_le_bytes(self) -> [u8; { $bits >> 3 }] {
              self.0.to_le_bytes()
            }
          )?
        }
      }

      impl Default for $name {
        #[inline]
        fn default() -> Self {
          Self($inner::new($default))
        }
      }

      $(
        impl From<[u8; { $bits >> 3 }]> for $name {
          #[inline]
          fn from(bytes: [u8; { $bits >> 3 }]) -> Self {
            Self($inner::from_be_bytes(bytes))
          }
        }

        impl From<$name> for [u8; { $bits >> 3 }] {
          #[inline]
          fn from(value: $name) -> Self {
            value.to_be_bytes()
          }
        }
      )?

      impl From<$inner> for $name {
        #[inline]
        fn from(val: $inner) -> Self {
          Self(val)
        }
      }

      impl From<$name> for $inner {
        #[inline]
        fn from(value: $name) -> Self {
          value.0
        }
      }

      impl Add for $name {
        type Output = Self;

        #[inline]
        fn add(self, rhs: Self) -> Self::Output {
          Self(self.0.checked_add(rhs.0).expect("attempt to add with overflow"))
        }
      }

      impl AddAssign for $name {
        #[inline]
        fn add_assign(&mut self, rhs: Self) {
          self.0 = self.0.checked_add(rhs.0).expect("attempt to add with overflow");
        }
      }

      impl Sub for $name {
        type Output = Self;

        fn sub(self, rhs: Self) -> Self::Output {
          let val = self.0.checked_sub(rhs.0).expect("attempt to subtract with overflow");
          if val < $inner::MIN {
            panic!("attempt to subtract with overflow");
          }

          Self(val)
        }
      }

      impl SubAssign for $name {
        fn sub_assign(&mut self, rhs: Self) {
          let val = self.0.checked_sub(rhs.0).expect("attempt to subtract with overflow");
          if val < $inner::MIN {
            panic!("attempt to subtract with overflow");
          }
          self.0 = val;
        }
      }

      $(impl_eq_and_ord!($name($inner < $upper) -> [$($ord_target),*]);)?

      $(impl_signed_eq_and_ord!($name($inner < $upper) -> [$($signed_ord_target),*]);)?

      $(impl_ops_for_ux_wrapper!($name($inner < $upper) -> [$($ops_target),*]);)?

      $(impl_try_from_for_ux_wrapper!($name($inner < $upper) -> [$($try_from_target),*]);)?

      $(impl_from_for_ux_wrapper!($name($inner < $upper) -> [$($from_target),*]);)?

      $(impl_into_for_ux_wrapper!($name($inner < $upper) -> [$($into_target),*]);)?
    )*
  };
}

ux_wrapper! {
  [doc = "Height which is used to configure the maximum tower height of a skiplist, it is a 5-bit unsigned integer."]
  Height(u5 < u8) {
    min: 1,
    default: 20,
    ord: [u8, u16, u32, u64, usize],
    signed_ord: [i8, i16, i32, i64, isize],
    ops: [u8, u16, u32, u64, usize],
    try_from: [u8, u16, u32, u64, usize],
    into: [u8, u16, u32, u64, usize, u128],
  },
  [doc = "KeySize which is used to represent a length of a key stored in the skiplist, it is a 27-bit unsigned integer."]
  KeySize(u27 < u32) {
    min: 0,
    default: u16::MAX as u32,
    ord: [u8, u16, u32, u64, usize],
    signed_ord: [i8, i16, i32, i64, isize],
    ops: [u8, u16, u32, u64, usize],
    try_from: [u32, usize],
    from: [u8, u16],
    into: [u32, u64, usize],
  },
}

dbutils::builder!(
  /// A value builder for the `SkipMap`s, which requires the value size for accurate allocation and a closure to build the value.
  pub ValueBuilder;
  /// A key builder for the `SkipMap`s, which requires the key size for accurate allocation and a closure to build the key.
  pub KeyBuilder;
);
