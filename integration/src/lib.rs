pub fn key(i: usize) -> kvstructs::Key {
    kvstructs::Key::from(format!("{:05}", i)).with_timestamp(0)
}

pub fn big_value(i: usize) -> kvstructs::Value {
    kvstructs::Value::from(format!("{:01048576}", i))
}

pub fn new_value(i: usize) -> kvstructs::ValueMut {
    use kvstructs::bytes::BufMut;

    let mut vm = kvstructs::ValueMut::default();
    vm.put_slice(format!("{:05}", i).as_bytes());
    vm
}
