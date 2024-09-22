use core::ops::Bound;

use dbutils::Comparator;
use rarena_allocator::Error as ArenaError;

use crate::{allocator::Sealed, Error};

use super::{Container, Options};

pub(crate) const KB: usize = 1 << 10;
const ARENA_SIZE: usize = 1 << 20;
#[cfg(feature = "std")]
const BIG_ARENA_SIZE: usize = 120 << 20;
pub(crate) const TEST_OPTIONS: Options = Options::new().with_capacity(ARENA_SIZE as u32);
const UNIFY_TEST_OPTIONS: Options = Options::new()
  .with_capacity(ARENA_SIZE as u32)
  .with_unify(true);
#[cfg(feature = "std")]
const BIG_TEST_OPTIONS: Options = Options::new().with_capacity(BIG_ARENA_SIZE as u32);
#[cfg(feature = "std")]
const UNIFY_BIG_TEST_OPTIONS: Options = Options::new()
  .with_capacity(BIG_ARENA_SIZE as u32)
  .with_unify(true);

pub(crate) mod full;

/// Only used for testing
pub fn key(i: usize) -> std::vec::Vec<u8> {
  format!("{:05}", i).into_bytes()
}

/// Only used for testing
#[cfg(feature = "std")]
pub fn big_value(i: usize) -> std::vec::Vec<u8> {
  format!("{:01048576}", i).into_bytes()
}

/// Only used for testing
pub fn new_value(i: usize) -> std::vec::Vec<u8> {
  format!("{:05}", i).into_bytes()
}

fn make_int_key(i: usize) -> std::vec::Vec<u8> {
  format!("{:05}", i).into_bytes()
}

fn make_value(i: usize) -> std::vec::Vec<u8> {
  format!("v{:05}", i).into_bytes()
}

#[macro_export]
macro_rules! container_tests {
  ($prefix:literal: $ty:ty) => {
    #[test]
    fn test_empty() {
      $crate::tests::empty(
        $crate::Builder::new()
          .with_capacity($crate::tests::KB as u32)
          .alloc::<$ty>()
          .unwrap(),
      );
    }

    #[test]
    fn test_empty_unify() {
      $crate::tests::empty(
        $crate::Builder::new()
          .with_capacity($crate::tests::KB as u32)
          .with_unify(true)
          .alloc::<$ty>()
          .unwrap(),
      );
    }

    #[test]
    #[cfg(feature = "memmap")]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::macro_metavars_in_unsafe)]
    fn test_empty_map_mut() {
      unsafe {
        let dir = ::tempfile::tempdir().unwrap();
        let p = dir
          .path()
          .join(::std::format!("test_{}_skipmap_empty_map_mut", $prefix));

        let map = $crate::Builder::new()
          .with_capacity($crate::tests::KB as u32)
          .with_create_new(true)
          .with_read(true)
          .with_write(true)
          .map_mut::<$ty, _>(p)
          .unwrap();
        $crate::tests::empty(map);
      }
    }

    #[test]
    #[cfg(feature = "memmap")]
    fn test_empty_map_anon() {
      $crate::tests::empty(
        $crate::Builder::new()
          .with_capacity($crate::tests::KB as u32)
          .map_anon::<$ty>()
          .unwrap(),
      );
    }

    #[test]
    #[cfg(feature = "memmap")]
    fn test_empty_map_anon_unify() {
      $crate::tests::empty(
        $crate::Builder::new()
          .with_capacity($crate::tests::KB as u32)
          .with_unify(true)
          .map_anon::<$ty>()
          .unwrap(),
      );
    }

    #[test]
    fn test_full() {
      $crate::tests::full(
        $crate::Builder::new()
          .with_capacity($crate::tests::KB as u32)
          .alloc::<$ty>()
          .unwrap(),
      );
    }

    #[test]
    fn test_full_unify() {
      $crate::tests::full(
        $crate::Builder::new()
          .with_capacity($crate::tests::KB as u32)
          .with_unify(true)
          .alloc::<$ty>()
          .unwrap(),
      );
    }

    #[test]
    #[cfg(feature = "memmap")]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::macro_metavars_in_unsafe)]
    fn test_full_map_mut() {
      unsafe {
        let dir = ::tempfile::tempdir().unwrap();
        let p = dir
          .path()
          .join(::std::format!("test_{}_skipmap_full_map_mut", $prefix));

        let map = $crate::Builder::new()
          .with_capacity($crate::tests::KB as u32)
          .with_create_new(true)
          .with_read(true)
          .with_write(true)
          .map_mut::<$ty, _>(p)
          .unwrap();
        $crate::tests::full(map);
      }
    }

    #[test]
    #[cfg(feature = "memmap")]
    fn test_full_map_anon() {
      $crate::tests::full(
        $crate::Builder::new()
          .with_capacity($crate::tests::KB as u32)
          .map_anon::<$ty>()
          .unwrap(),
      );
    }

    #[test]
    #[cfg(feature = "memmap")]
    fn test_full_map_anon_unify() {
      $crate::tests::full(
        $crate::Builder::new()
          .with_capacity($crate::tests::KB as u32)
          .with_unify(true)
          .map_anon::<$ty>()
          .unwrap(),
      );
    }
  };
}

pub(crate) fn empty<M: Container>(l: M)
where
  M::Comparator: Comparator,
{
  let mut it = l.iter();

  assert!(it.seek_lower_bound(Bound::Unbounded).is_none());
  assert!(it.seek_upper_bound(Bound::Unbounded).is_none());
  assert!(it.seek_lower_bound(Bound::Included(b"aaa")).is_none());
  assert!(it.seek_upper_bound(Bound::Excluded(b"aaa")).is_none());
  assert!(it.seek_lower_bound(Bound::Excluded(b"aaa")).is_none());
  assert!(it.seek_upper_bound(Bound::Included(b"aaa")).is_none());
  assert!(l.first().is_none());
  assert!(l.last().is_none());
  assert!(l.get(b"aaa").is_none());
  assert!(!l.contains_key(b"aaa"));
  assert!(l.allocated() > 0);
  assert!(l.capacity() > 0);
  assert_eq!(l.remaining(), l.capacity() - l.allocated());
}

pub(crate) fn full<M>(l: M)
where
  M: super::map::Map,
  M::Comparator: Comparator,
  <M::Allocator as Sealed>::Trailer: Default,
{
  let mut found_arena_full = false;

  for i in 0..100 {
    if let Err(e) = l.get_or_insert(&make_int_key(i), &make_value(i)) {
      assert!(matches!(
        e,
        Error::Arena(ArenaError::InsufficientSpace { .. })
      ));
      found_arena_full = true;
      break;
    }
  }

  assert!(found_arena_full);
}
