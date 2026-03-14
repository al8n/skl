/// Only used for testing
pub fn key(i: usize) -> Vec<u8> {
  format!("{:05}", i).into_bytes()
}

/// Only used for testing
pub fn big_value(i: usize) -> Vec<u8> {
  let mut v = ::std::format!("{}", i).into_bytes();
  v.resize(1048576, b'0');
  v
}

/// Only used for testing
pub fn new_value(i: usize) -> Vec<u8> {
  format!("{:05}", i).into_bytes()
}
