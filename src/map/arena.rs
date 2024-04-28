use super::{super::*, *};
use crate::sync::{AtomicMut, AtomicPtr};
use core::{ptr::NonNull, slice};

mod shared;
use shared::Shared;

/// Arena should be lock-free
pub(super) struct Arena {
  data_ptr: NonNull<u8>,
  inner: AtomicPtr<()>,
  cap: usize,
}

impl core::fmt::Debug for Arena {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    let inner = self.inner();
    inner.as_slice().fmt(f)
  }
}

impl Arena {
  #[inline]
  pub(super) fn new_vec(n: usize) -> Self {
    let mut inner = Shared::new_vec(n.max(Node::MAX_NODE_SIZE));
    let data_ptr = unsafe { NonNull::new_unchecked(inner.as_mut_ptr()) };
    Self {
      cap: inner.cap(),
      inner: AtomicPtr::new(Box::into_raw(Box::new(inner)) as _),
      data_ptr,
    }
  }

  #[cfg(all(feature = "mmap", not(target_family = "wasm")))]
  #[inline]
  pub(super) fn new_mmap(n: usize, file: std::fs::File, lock: bool) -> std::io::Result<Self> {
    let mut inner = Shared::new_mmaped(n.max(Node::MAX_NODE_SIZE), file, lock)?;
    let data_ptr = unsafe { NonNull::new_unchecked(inner.as_mut_ptr()) };
    Ok(Self {
      cap: inner.cap(),
      inner: AtomicPtr::new(Box::into_raw(Box::new(inner)) as _),
      data_ptr,
    })
  }

  #[cfg(all(feature = "mmap", not(target_family = "wasm")))]
  #[inline]
  pub(super) fn new_anonymous_mmap(n: usize) -> std::io::Result<Self> {
    let mut inner = Shared::new_mmaped_anon(n.max(Node::MAX_NODE_SIZE))?;
    let data_ptr = unsafe { NonNull::new_unchecked(inner.as_mut_ptr()) };
    Ok(Self {
      cap: inner.cap(),
      inner: AtomicPtr::new(Box::into_raw(Box::new(inner)) as _),
      data_ptr,
    })
  }

  pub(super) fn put_key(&self, key: KeyRef<'_>) -> (u32, bool) {
    let version = key.version();
    if version == 0 {
      let key_size = key.len();
      let offset = self.allocate(key_size as u32);
      unsafe {
        core::ptr::copy_nonoverlapping(
          key.as_ref().as_ptr(),
          self.get_data_ptr_mut(offset as usize),
          key_size,
        );
      }
      (offset, false)
    } else {
      let key_size = TIMESTAMP_SIZE + key.len();
      let offset = self.allocate(key_size as u32);
      unsafe {
        let buf = slice::from_raw_parts_mut(self.get_data_ptr_mut(offset as usize), key_size);
        buf[..key_size - TIMESTAMP_SIZE].copy_from_slice(key.as_ref());
        buf[key_size - TIMESTAMP_SIZE..].copy_from_slice(&version.to_be_bytes());
      }
      (offset, true)
    }
  }

  pub(super) fn put_val(&self, val: ValueRef<'_>) -> u32 {
    let l = val.encoded_size();
    let offset = self.allocate(l as u32);
    let buf = unsafe { slice::from_raw_parts_mut(self.get_data_ptr_mut(offset as usize), l) };
    val.encode(buf);
    offset
  }

  pub(super) fn new_node(
    &self,
    key: KeyRef<'_>,
    val: ValueRef<'_>,
    height: usize,
  ) -> (*mut Node, u32) {
    let node_offset = self.put_node(height);

    let key_len = key.len();
    let (key_offset, timestamped) = self.put_key(key);
    let v_encode_size = val.encoded_size() as u32;
    let val = Node::encode_value(self.put_val(val), v_encode_size);

    let (node, offset) = unsafe {
      let (node_ptr, offset) = self.get_node(node_offset);
      (&mut *node_ptr, offset)
    };
    node.key_offset = key_offset;
    node.key_size = key_len as u16;
    node.height = height as u8;
    node.timestamped = timestamped as u8;
    node.val = AtomicU64::new(val);
    (node, offset)
  }

  pub(super) fn get_node(&self, offset: u32) -> (*mut Node, u32) {
    if offset == 0 || offset >= self.cap as u32 {
      return (ptr::null_mut(), 0);
    }
    (
      self.get_data_ptr_mut(offset as usize).cast(),
      offset + Node::TOWER_OFFSET as u32,
    )
  }

  pub(super) fn get_key<'a, 'b: 'a>(
    &'a self,
    offset: u32,
    size: u16,
    timestamped: bool,
  ) -> KeyRef<'b> {
    let size = size as usize;
    let ptr = self.get_data_ptr(offset as usize);
    // Safety: the underlying ptr will never be freed until the Arena is dropped.
    unsafe {
      KeyRef {
        version: if timestamped {
          u64::from_be_bytes(
            slice::from_raw_parts(ptr.add(size), TIMESTAMP_SIZE)
              .try_into()
              .unwrap(),
          )
        } else {
          0
        },
        data: slice::from_raw_parts(ptr, size),
      }
    }
  }

  pub(super) fn get_val<'a, 'b: 'a>(&'a self, offset: u32, size: u32) -> ValueRef<'b> {
    let ptr = self.get_data_ptr(offset as usize);
    // Safety: the underlying ptr will never be freed until the Arena is dropped.
    unsafe { ValueRef::decode(slice::from_raw_parts(ptr, size as usize)) }
  }

  pub(super) fn get_node_offset(&self, node: *const Node) -> u32 {
    if node.is_null() {
      return 0;
    }
    (node as usize - self.data_ptr.as_ptr() as usize) as u32
  }

  #[inline]
  pub(super) const fn cap(&self) -> usize {
    self.cap
  }

  #[inline]
  pub(super) fn tower<'a>(&self, offset: usize, height: usize) -> &'a crate::sync::AtomicU32 {
    unsafe {
      let ptr = self.get_data_ptr(offset + height * mem::size_of::<crate::sync::AtomicU32>());
      &*ptr.cast()
    }
  }
}

impl Arena {
  #[inline]
  fn allocate(&self, sz: u32) -> u32 {
    let offset = self.inner().n.fetch_add(sz, Ordering::SeqCst) + sz;
    assert!(
      (offset as usize) <= self.cap,
      "Arena: ARENA does not have enough space"
    );
    offset - sz
  }

  /// Compute the amount of the tower that will never be used, since the height
  /// is less than Node::MAX_HEIGHT.
  #[inline(always)]
  fn unused_size(&self, height: usize) -> usize {
    (Node::MAX_HEIGHT - height) * Node::OFFSET_SIZE
  }

  fn put_node(&self, height: usize) -> u32 {
    // Compute the amount of the tower that will never be used, since the height
    // is less than maxHeight.
    let unused_size = self.unused_size(height);

    // Pad the allocation with enough bytes to ensure pointer alignment.
    let l = (Node::MAX_NODE_SIZE - unused_size + Node::NODE_ALIGN) as u32;
    let n = self.allocate(l);

    // Return the aligned offset.
    (n + Node::NODE_ALIGN as u32) & !(Node::NODE_ALIGN as u32)
  }

  #[inline]
  fn inner(&self) -> &Shared {
    unsafe { &*(self.inner.load(Ordering::Acquire) as *const Shared) }
  }

  #[allow(clippy::mut_from_ref)]
  #[inline]
  fn inner_mut(&self) -> &mut Shared {
    unsafe { &mut *(self.inner.load(Ordering::Acquire) as *mut Shared) }
  }

  #[inline]
  fn get_data_ptr(&self, offset: usize) -> *const u8 {
    unsafe { self.data_ptr.as_ptr().add(offset) }
  }

  #[inline]
  fn get_data_ptr_mut(&self, offset: usize) -> *mut u8 {
    unsafe { self.data_ptr.as_ptr().add(offset) }
  }
}

unsafe impl Send for Arena {}
unsafe impl Sync for Arena {}

impl Clone for Arena {
  fn clone(&self) -> Self {
    let inner = self.inner_mut();
    let old_size = inner.refs.fetch_add(1, Ordering::Relaxed);
    if old_size > usize::MAX >> 1 {
      abort();
    }

    Self {
      cap: self.cap,
      inner: AtomicPtr::new(inner as *mut Shared as _),
      data_ptr: self.data_ptr,
    }
  }
}

impl Drop for Arena {
  fn drop(&mut self) {
    unsafe {
      self.inner.with_mut(|shared| {
        let shared: *mut Shared = shared.cast();
        // `Shared` storage... follow the drop steps from Arc.
        if (*shared).refs.fetch_sub(1, Ordering::Release) != 1 {
          return;
        }

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
        (*shared).refs.load(Ordering::Acquire);
        // Drop the data
        drop(Box::from_raw(shared));
      });
    }
  }
}

#[inline(never)]
#[cold]
fn abort() -> ! {
  #[cfg(feature = "std")]
  {
    std::process::abort();
  }

  #[cfg(not(feature = "std"))]
  {
    struct Abort;
    impl Drop for Abort {
      fn drop(&mut self) {
        panic!();
      }
    }
    let _a = Abort;
    panic!("abort");
  }
}
