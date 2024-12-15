#![doc = include_str!("../README.md")]
#![cfg_attr(not(all(feature = "std", test)), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![deny(missing_docs)]
#![allow(
  unexpected_cfgs,
  clippy::type_complexity,
  clippy::mut_from_ref,
  rustdoc::bare_urls
)]

#[cfg(not(feature = "std"))]
extern crate alloc as std;

#[cfg(feature = "std")]
extern crate std;

mod allocator;
use core::marker::PhantomData;

pub use allocator::GenericAllocator;

/// The dynamic key-value type `SkipMap`s.
pub mod dynamic;

/// The generic key-value type `SkipMap`s.
pub mod generic;

/// Error types for the `SkipMap`s.
pub mod error;

/// Options for the `SkipMap`s.
#[macro_use]
pub mod options;
use dbutils::types::{LazyRef, TypeRef};
pub use options::Options;

mod traits;
pub use traits::Arena;

mod types;
pub use types::*;

#[cfg(any(
  all(test, not(miri)),
  all_skl_tests,
  test_generic_unsync_map,
  test_generic_unsync_versioned,
  test_generic_sync_map,
  test_generic_sync_versioned,
  test_generic_sync_map_concurrent,
  test_generic_sync_multiple_version_concurrent,
  test_generic_sync_map_concurrent_with_optimistic_freelist,
  test_generic_sync_multiple_version_concurrent_with_optimistic_freelist,
  test_generic_sync_map_concurrent_with_pessimistic_freelist,
  test_generic_sync_multiple_version_concurrent_with_pessimistic_freelist,
  test_dynamic_unsync_map,
  test_dynamic_unsync_versioned,
  test_dynamic_sync_map,
  test_dynamic_sync_versioned,
  test_dynamic_sync_map_concurrent,
  test_dynamic_sync_multiple_version_concurrent,
  test_dynamic_sync_map_concurrent_with_optimistic_freelist,
  test_dynamic_sync_multiple_version_concurrent_with_optimistic_freelist,
  test_dynamic_sync_map_concurrent_with_pessimistic_freelist,
  test_dynamic_sync_multiple_version_concurrent_with_pessimistic_freelist,
))]
mod tests;

pub use among;
pub use either;
pub use rarena_allocator::Allocator;

const MAX_HEIGHT: usize = 1 << 5;
const MIN_VERSION: Version = Version::MIN;
/// The tombstone value size, if a node's value size is equal to this value, then it is a tombstone.
const REMOVE: u32 = u32::MAX;

/// A helper struct for caching splice information
pub struct Inserter<'a, P> {
  spl: [Splice<P>; crate::MAX_HEIGHT],
  height: u32,
  _m: core::marker::PhantomData<&'a ()>,
}

impl<P: allocator::NodePointer> Default for Inserter<'_, P> {
  #[inline]
  fn default() -> Self {
    Self {
      spl: [
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
        Splice::default(),
      ],
      height: 0,
      _m: core::marker::PhantomData,
    }
  }
}

#[derive(Debug, Clone, Copy)]
struct Splice<P> {
  prev: P,
  next: P,
}

impl<P: allocator::NodePointer> Default for Splice<P> {
  #[inline]
  fn default() -> Self {
    Self {
      prev: P::NULL,
      next: P::NULL,
    }
  }
}

struct FindResult<P> {
  // both key and version are equal.
  found: bool,
  // only key is equal.
  found_key: Option<allocator::Pointer>,
  splice: Splice<P>,
  curr: Option<P>,
}

/// Utility function to generate a random height for a new node.
#[cfg(feature = "std")]
pub fn random_height(max_height: Height) -> Height {
  use rand::{thread_rng, Rng};
  let mut rng = thread_rng();
  let rnd: u32 = rng.gen();
  let mut h = 1;
  let max_height = max_height.to_usize();

  while h < max_height && rnd <= PROBABILITIES[h] {
    h += 1;
  }
  Height::from_u8_unchecked(h as u8)
}

/// Utility function to generate a random height for a new node.
#[cfg(not(feature = "std"))]
pub fn random_height(max_height: Height) -> Height {
  use rand::{rngs::OsRng, Rng};

  let max_height = max_height.to_usize();
  let rnd: u32 = OsRng.gen();
  let mut h = 1;

  while h < max_height && rnd <= PROBABILITIES[h] {
    h += 1;
  }
  Height::from_u8_unchecked(h as u8)
}

/// Precompute the skiplist probabilities so that only a single random number
/// needs to be generated and so that the optimal pvalue can be used (inverse
/// of Euler's number).
const PROBABILITIES: [u32; MAX_HEIGHT] = {
  const P: f64 = 1.0 / core::f64::consts::E;

  let mut probabilities = [0; MAX_HEIGHT];
  let mut p = 1f64;

  let mut i = 0;
  while i < MAX_HEIGHT {
    probabilities[i] = ((u32::MAX as f64) * p) as u32;
    p *= P;
    i += 1;
  }

  probabilities
};

#[inline]
const fn encode_value_pointer(offset: u32, val_size: u32) -> u64 {
  (val_size as u64) << 32 | offset as u64
}

#[inline]
const fn decode_value_pointer(value: u64) -> (u32, u32) {
  let offset = value as u32;
  let val_size = (value >> 32) as u32;
  (offset, val_size)
}

#[inline]
const fn encode_key_size_and_height(key_size: u32, height: u8) -> u32 {
  // first 27 bits for key_size, last 5 bits for height.
  key_size << 5 | height as u32
}

#[inline]
const fn decode_key_size_and_height(size: u32) -> (u32, u8) {
  let key_size = size >> 5;
  let height = (size & 0b11111) as u8;
  (key_size, height)
}

mod common {
  #[cfg(not(feature = "loom"))]
  pub(crate) use core::sync::atomic::*;

  #[cfg(feature = "loom")]
  pub(crate) use loom::sync::atomic::*;
}

macro_rules! node {
  (
    $(#[$meta:meta])*
    struct $name:ident {
      flags = $flags:expr;

      $($field:ident:$field_ty:ty = $default:expr;)*

      {
        type Link = $link:ty;

        type ValuePointer = $value_pointer:ty;

        type Pointer = $pointer:ty;

        fn set_version(&mut self, version: Version) {
          $(
            self.$version_setter:ident = version;
          )?
        }

        $($tt:tt)*
      }
    }
  ) => {
    $(#[$meta])*
    #[repr(C)]
    pub struct $name {
      // A byte slice is 24 bytes. We are trying to save space here.
      /// Multiple parts of the value are encoded as a single u64 so that it
      /// can be atomically loaded and stored:
      ///   value offset: u32 (bits 0-31)
      ///   value size  : u32 (bits 32-63)
      value: $value_pointer,
      // Immutable. No need to lock to access key.
      key_offset: u32,
      // Immutable. No need to lock to access key.
      key_size_and_height: u32,

      $($field: $field_ty,)*

      // ** DO NOT REMOVE BELOW COMMENT**
      // The below field will be attached after the node, have to comment out
      // this field, because each node will not use the full height, the code will
      // not allocate the full size of the tower.
      //
      // Most nodes do not need to use the full height of the tower, since the
      // probability of each successive level decreases exponentially. Because
      // these elements are never accessed, they do not need to be allocated.
      // Therefore, when a node is allocated in the arena, its memory footprint
      // is deliberately truncated to not include unneeded tower elements.
      //
      // All accesses to elements should use CAS operations, with no need to lock.
      // pub(super) tower: [Link; self.opts.max_height],
    }

    impl ::core::fmt::Debug for $name {
      fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
        let (key_size, height) = $crate::decode_key_size_and_height(self.key_size_and_height);
        let (value_offset, value_size) = self.value.load();
        f.debug_struct(stringify!($name))
          .field("value_offset", &value_offset)
          .field("value_size", &value_size)
          .field("key_offset", &self.key_offset)
          .field("key_size", &key_size)
          .field("height", &height)
          $(.field("version", &self.$version_setter))?
          .finish()
      }
    }

    impl $crate::allocator::Node for $name {
      type Link = $link;

      type ValuePointer = $value_pointer;

      type Pointer = NodePointer;

      #[inline]
      fn full(value_offset: u32, max_height: u8) -> Self {
        Self {
          value: <$value_pointer>::new(value_offset, 0),
          key_offset: 0,
          key_size_and_height: $crate::encode_key_size_and_height(0, max_height),
          $($field: $default,)*
        }
      }

      #[inline]
      fn flags() -> crate::types::internal::Flags {
        $flags
      }

      #[inline]
      fn value_pointer(&self) -> &Self::ValuePointer {
        &self.value
      }

      #[inline]
      fn set_value_pointer(&mut self, offset: u32, size: u32) {
        self.value = <$value_pointer>::new(offset, size);
      }

      #[inline]
      fn set_key_size_and_height(&mut self, key_size_and_height: u32) {
        self.key_size_and_height = key_size_and_height;
      }

      #[inline]
      fn set_key_offset(&mut self, key_offset: u32) {
        self.key_offset = key_offset;
      }

      #[inline]
      fn set_version(&mut self, _version: Version) {
        $(self.$version_setter = _version)?
      }
    }

    $($tt)*
  };
}

/// Implementations for concurrent environments.
mod sync;

/// Implementations for single-threaded environments.
mod unsync;

mod ref_counter;

#[inline]
fn ty_ref<'a, T: dbutils::types::Type + ?Sized>(src: &'a [u8]) -> T::Ref<'a> {
  unsafe { <T::Ref<'a> as dbutils::types::TypeRef<'a>>::from_slice(src) }
}

// /// A marker trait for the state of the entry.
// pub trait State<'a>: sealed::Sealed<'a> {}

// impl<'a, T: sealed::Sealed<'a>> State<'a> for T {}

pub use dbutils::state::{Active, MaybeTombstone, State};

trait Data {
  type Active: ?Sized;
  type MaybeTombstone: ?Sized;
}

impl<T> Data for T {
  type Active = T;
  type MaybeTombstone = Option<T>;
}

trait Transformer<'a> {
  type Output;

  fn from_bytes(src: Option<&'a [u8]>) -> Self;

  fn transform(&self) -> Self::Output;
}

/// Transformable
pub trait Transformable {
  /// The output type of this transform.
  type Output;

  /// The input type of this transform.
  type Input;

  /// Returns the input state.
  fn input(&self) -> Self::Input;

  /// Converts the input state to the state.
  fn from_input(input: Self::Input) -> Self
  where
    Self: Sized;

  /// Returns the output after transformring.
  fn transform(&self) -> Self::Output;

  /// Returns `true` the state is valid or not.
  fn validate(&self) -> bool;

  /// Returns `true` if this state will never be invalid.
  fn always_valid() -> bool;
}

impl Transformable for &[u8] {
  type Output = Self;
  type Input = Option<Self>;

  #[inline]
  fn input(&self) -> Self::Input {
    Some(self)
  }

  #[inline]
  fn from_input(input: Self::Input) -> Self {
    input.expect("entry in Active state must have value")
  }

  #[inline]
  fn transform(&self) -> Self::Output {
    self
  }

  #[inline]
  fn validate(&self) -> bool {
    true
  }

  #[inline]
  fn always_valid() -> bool {
    true
  }
}

impl<'a, T> Transformable for LazyRef<'a, T>
where
  T: TypeRef<'a>,
{
  type Input = Option<&'a [u8]>;
  type Output = T;

  #[inline]
  fn input(&self) -> Self::Input {
    Some(self.raw().expect("entry in Active state must have value"))
  }

  #[inline]
  fn from_input(input: Self::Input) -> Self {
    unsafe { LazyRef::from_raw(input.expect("entry in Active state must have value")) }
  }

  #[inline]
  fn transform(&self) -> Self::Output {
    *self.get()
  }

  #[inline]
  fn validate(&self) -> bool {
    true
  }

  #[inline]
  fn always_valid() -> bool {
    true
  }
}

impl<'a> Transformable for Option<&'a [u8]> {
  type Output = Option<&'a [u8]>;
  type Input = Option<&'a [u8]>;

  #[inline]
  fn input(&self) -> Self::Input {
    *self
  }

  #[inline]
  fn from_input(input: Self::Input) -> Self {
    input
  }

  #[inline]
  fn transform(&self) -> Self::Output {
    self.as_ref().copied()
  }

  #[inline]
  fn validate(&self) -> bool {
    self.is_some()
  }

  #[inline]
  fn always_valid() -> bool {
    false
  }
}

impl<'a, T> Transformable for Option<LazyRef<'a, T>>
where
  T: TypeRef<'a>,
{
  type Output = Option<T>;
  type Input = Option<&'a [u8]>;

  #[inline]
  fn input(&self) -> Self::Input {
    self
      .as_ref()
      .map(|v| v.raw().expect("entry must have a raw value"))
  }

  #[inline]
  fn from_input(input: Self::Input) -> Self {
    input.map(|v| unsafe { LazyRef::from_raw(v) })
  }

  #[inline]
  fn transform(&self) -> Self::Output {
    self.as_ref().map(|v| *v.get())
  }

  #[inline]
  fn validate(&self) -> bool {
    self.is_some()
  }

  #[inline]
  fn always_valid() -> bool {
    false
  }
}

/// a
#[repr(transparent)]
struct TypeState<'a, S>
where
  S: ?Sized + State<'a>,
{
  _m: PhantomData<&'a S>,
  data: S::Data,
}

impl<'a, S> Clone for TypeState<'a, S>
where
  S: ?Sized + State<'a>,
  S::Data: Clone,
{
  fn clone(&self) -> Self {
    Self {
      _m: PhantomData,
      data: self.data.clone(),
    }
  }
}

impl<'a> Transformer<'a> for TypeState<'a, Active<&'a [u8]>> {
  type Output = &'a [u8];

  fn from_bytes(src: Option<&'a [u8]>) -> Self {
    Self {
      _m: PhantomData,
      data: src.expect("entry in Active state must have value"),
    }
  }

  #[inline]
  fn transform(&self) -> Self::Output {
    self.data
  }
}

impl<'a, T> Transformer<'a> for TypeState<'a, Active<LazyRef<'a, T>>>
where
  T: TypeRef<'a>,
{
  type Output = T;

  #[inline]
  fn from_bytes(src: Option<&'a [u8]>) -> Self {
    Self {
      _m: PhantomData,
      data: unsafe { LazyRef::from_raw(src.expect("entry in Active state must have value")) },
    }
  }

  #[inline]
  fn transform(&self) -> Self::Output {
    *self.data.get()
  }
}

impl<'a> Transformer<'a> for TypeState<'a, MaybeTombstone<&'a [u8]>> {
  type Output = Option<&'a [u8]>;

  #[inline]
  fn from_bytes(src: Option<&'a [u8]>) -> Self {
    Self {
      _m: PhantomData,
      data: src,
    }
  }

  #[inline]
  fn transform(&self) -> Self::Output {
    self.data.as_ref().copied()
  }
}

impl<'a, T> Transformer<'a> for TypeState<'a, MaybeTombstone<LazyRef<'a, T>>>
where
  T: TypeRef<'a>,
{
  type Output = Option<T>;

  #[inline]
  fn from_bytes(src: Option<&'a [u8]>) -> Self {
    Self {
      _m: PhantomData,
      data: src.map(|v| unsafe { LazyRef::from_raw(v) }),
    }
  }

  #[inline]
  fn transform(&self) -> Self::Output {
    self.data.as_ref().map(|v| *v.get())
  }
}
