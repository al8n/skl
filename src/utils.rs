use crate::{key::Key, value::Value};

/// Only used for testing

pub fn key(i: usize) -> Key {
  Key::from(format!("{:05}", i)).with_ttl(0)
}

/// Only used for testing
pub fn big_value(i: usize) -> Value {
  Value::from(format!("{:01048576}", i))
}

/// Only used for testing
pub fn new_value(i: usize) -> Value {
  use bytes::{BufMut, BytesMut};

  let mut vm = BytesMut::default();
  vm.put_slice(format!("{:05}", i).as_bytes());
  Value::from(vm.freeze())
}
