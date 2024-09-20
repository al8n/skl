#![allow(warnings)]

use super::*;
use crate::Descend;

use std::format;

use std::sync::Arc;

use rarena_allocator::Freelist;
#[cfg(feature = "std")]
use wg::WaitGroup;

const ARENA_SIZE: usize = 1 << 20;
#[cfg(feature = "std")]
const BIG_ARENA_SIZE: usize = 120 << 20;
const TEST_OPTIONS: Options = Options::new().with_capacity(ARENA_SIZE as u32);
const UNIFY_TEST_OPTIONS: Options = Options::new()
  .with_capacity(ARENA_SIZE as u32)
  .with_unify(true);
#[cfg(feature = "std")]
const BIG_TEST_OPTIONS: Options = Options::new().with_capacity(BIG_ARENA_SIZE as u32);
#[cfg(feature = "std")]
const UNIFY_BIG_TEST_OPTIONS: Options = Options::new()
  .with_capacity(BIG_ARENA_SIZE as u32)
  .with_unify(true);

fn run(f: impl Fn() + Send + Sync + 'static) {
  f();
}

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

#[test]
fn test_encode_decode_key_size() {
  // Test cases
  let test_cases = [
    (0, 0),                       // Minimum values
    (1, 1),                       // Small values
    (0x1FFFFFF, 0),               // Maximum key_size, minimum height
    (0, 0b11111),                 // Minimum key_size, maximum height
    (0x1FFFFFF, 0b11111),         // Maximum values
    (0x1FFFFFF - 1, 0b11111 - 1), // One less than maximum values
    (12345678, 31),               // Random values
    (0, 1),                       // Edge case: Minimum key_size, small height
    (1, 0),                       // Edge case: Small key_size, minimum height
  ];

  for &(key_size, height) in &test_cases {
    let encoded = encode_key_size_and_height(key_size, height);
    let (decoded_key_size, decoded_height) = decode_key_size_and_height(encoded);

    assert_eq!(key_size, decoded_key_size);
    assert_eq!(height, decoded_height);
  }
}

#[cfg(any(all(test, not(miri)), test_sync_full,))]
mod full;

#[cfg(any(all(test, not(miri)), test_sync_map,))]
mod map;

#[cfg(any(all(test, not(miri)), test_sync_trailed,))]
mod trailed;

#[cfg(any(all(test, not(miri)), test_sync_versioned,))]
mod versioned;
