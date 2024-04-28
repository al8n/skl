/// Only used for testing
pub fn key(i: usize) -> Vec<u8> {
  format!("{:05}", i).into_bytes()
}

/// Only used for testing
pub fn big_value(i: usize) -> Vec<u8> {
  format!("{:01048576}", i).into_bytes()
}

/// Only used for testing
pub fn new_value(i: usize) -> Vec<u8> {
  format!("{:05}", i).into_bytes()
}
