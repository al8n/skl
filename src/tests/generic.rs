#[cfg(any(
  all(test, not(miri)),
  all_skl_tests,
  test_generic_unsync_map,
  test_generic_sync_map,
  test_generic_sync_map_concurrent,
  test_generic_sync_map_concurrent_with_optimistic_freelist,
  test_generic_sync_map_concurrent_with_pessimistic_freelist,
))]
pub(crate) mod map;

#[cfg(any(
  all(test, not(miri)),
  all_skl_tests,
  test_generic_unsync_versioned,
  test_generic_sync_versioned,
  test_generic_sync_multiple_version_concurrent,
  test_generic_sync_multiple_version_concurrent_with_optimistic_freelist,
  test_generic_sync_multiple_version_concurrent_with_pessimistic_freelist,
))]
pub(crate) mod multiple_version;

use crate::generic::{Ascend, Builder};

use super::*;

pub(crate) const TEST_OPTIONS: Builder<Ascend<[u8]>> =
  Builder::with(Ascend::new()).with_capacity(ARENA_SIZE as u32);
pub(crate) const TEST_FULL_OPTIONS: Builder<Ascend<[u8]>> =
  Builder::with(Ascend::new()).with_capacity(1024);
pub(crate) const TEST_OPTIONS_WITH_OPTIMISTIC_FREELIST: Builder<Ascend<[u8]>> =
  Builder::with(Ascend::new())
    .with_capacity(ARENA_SIZE as u32)
    .with_freelist(rarena_allocator::Freelist::Optimistic);
pub(crate) const TEST_OPTIONS_WITH_PESSIMISTIC_FREELIST: Builder<Ascend<[u8]>> =
  Builder::with(Ascend::new())
    .with_capacity(ARENA_SIZE as u32)
    .with_freelist(rarena_allocator::Freelist::Pessimistic);
// pub(crate) const TEST_HIGH_COMPRESSION_OPTIONS: Options = Options::new()
//   .with_capacity(ARENA_SIZE as u32)
//   .with_compression_policy(crate::CompressionPolicy::High);
#[cfg(all(
  all(feature = "std", not(miri)),
  any(
    all(test, not(miri)),
    all_skl_tests,
    test_generic_sync_full,
    test_generic_sync_map,
    test_generic_sync_trailed,
    test_generic_sync_versioned,
  )
))]
const BIG_ARENA_SIZE: usize = 120 << 20;

#[cfg(all(
  all(feature = "std", not(miri)),
  any(
    all(test, not(miri)),
    all_skl_tests,
    test_generic_sync_full,
    test_generic_sync_map,
    test_generic_sync_trailed,
    test_generic_sync_versioned,
  )
))]
pub(crate) const BIG_TEST_OPTIONS: Builder<Ascend<[u8]>> =
  Builder::with(Ascend::new()).with_capacity(BIG_ARENA_SIZE as u32);
