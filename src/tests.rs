#![allow(dead_code)]

// #[cfg(any(
//   all(test, not(miri)),
//   all_skl_tests,
//   test_generic_unsync_map,
//   test_generic_unsync_versioned,
//   test_generic_sync_map,
//   test_generic_sync_versioned,
//   test_generic_sync_map_concurrent,
//   test_generic_sync_multiple_version_concurrent,
//   test_generic_sync_map_concurrent_with_optimistic_freelist,
//   test_generic_sync_multiple_version_concurrent_with_optimistic_freelist,
//   test_generic_sync_map_concurrent_with_pessimistic_freelist,
//   test_generic_sync_multiple_version_concurrent_with_pessimistic_freelist,
// ))]
#[cfg(test)]
pub mod generic;

#[cfg(any(
  all(test, not(miri)),
  all_skl_tests,
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
pub mod dynamic;

pub(crate) const KB: usize = 1 << 10;
const ARENA_SIZE: usize = 1 << 20;

/// Only used for testing
pub fn key(i: usize) -> std::vec::Vec<u8> {
  ::std::format!("{:05}", i).into_bytes()
}

/// Only used for testing
pub fn int_key(i: usize) -> std::vec::Vec<u8> {
  ::std::format!("{i}").into_bytes()
}

/// Only used for testing
#[cfg(all(feature = "std", not(miri)))]
pub fn big_value(i: usize) -> std::vec::Vec<u8> {
  ::std::format!("{:01048576}", i).into_bytes()
}

/// Only used for testing
pub fn new_value(i: usize) -> std::vec::Vec<u8> {
  ::std::format!("{:05}", i).into_bytes()
}

fn make_int_key(i: usize) -> std::vec::Vec<u8> {
  ::std::format!("{:05}", i).into_bytes()
}

fn make_value(i: usize) -> std::vec::Vec<u8> {
  ::std::format!("v{:05}", i).into_bytes()
}

#[macro_export]
#[doc(hidden)]
macro_rules! __unit_tests {
  ($mod:path |$prefix:literal, $ty:ty, $opts:path| {
    $(
      $(#[cfg($cfg:meta)])?
      $name:ident,
    )*
  }) => {
    $(
      $crate::__unit_test_expand!(
        $(#[cfg($cfg)])?
        $mod |$prefix, $name, $ty, $opts|
      );
    )*
  };
}

#[macro_export]
#[doc(hidden)]
macro_rules! __unit_test_expand {
  (
    $(#[cfg($cfg:meta)])?
    $fn:path |$prefix:literal, $name:ident, $ty:ty, $opts: path|
  ) => {
    paste::paste! {
      #[test]
      $(#[cfg($cfg)])?
      fn [< test_ $name >]() {
        $fn::$name(
          $opts
            .alloc::<$ty>()
            .unwrap(),
        );
      }

      #[test]
      $(#[cfg($cfg)])?
      fn [< test_ $name _unify >]() {
        $fn::$name(
          $opts
            .with_unify(true)
            .alloc::<$ty>()
            .unwrap(),
        );
      }

      #[test]
      $(#[cfg($cfg)])?
      #[cfg(feature = "memmap")]
      #[cfg_attr(miri, ignore)]
      #[allow(clippy::macro_metavars_in_unsafe)]
      fn [< test_ $name _map_mut >]() {
        unsafe {
          let dir = ::tempfile::tempdir().unwrap();
          let p = dir
            .path()
            .join(::std::format!("test_{}_skipmap_{}_map_mut", $prefix, stringify!($name)));
          $fn::$name(
            $opts
              .with_create_new(true)
              .with_read(true)
              .with_write(true)
              .map_mut::<$ty, _>(p)
              .unwrap(),
          );
        }
      }

      #[test]
      $(#[cfg($cfg)])?
      #[cfg(feature = "memmap")]
      fn [< test_ $name _map_anon >] () {
        $fn::$name(
          $opts
            .map_anon::<$ty>()
            .unwrap(),
        );
      }

      #[test]
      $(#[cfg($cfg)])?
      #[cfg(feature = "memmap")]
      fn [< test_ $name _map_anon_unify >]() {
        $fn::$name(
          $opts
            .with_unify(true)
            .map_anon::<$ty>()
            .unwrap(),
        );
      }
    }
  };
}
