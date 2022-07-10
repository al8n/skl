use crate::{
    sync::{Arc, AtomicU32, AtomicU64, Ordering},
    Node,
};
use alloc::{vec, vec::Vec};
use core::ptr::{null, null_mut, slice_from_raw_parts, write, write_bytes, NonNull};
use core::{
    cell::UnsafeCell,
    mem::{self, ManuallyDrop},
};
use core::{
    fmt::{Debug, Formatter},
    ops::Add,
};
use kvstructs::Key;
use kvstructs::{
    bytes::Bytes,
    raw_pointer::{RawKeyPointer, RawValuePointer},
    KeyExt, KeyRef, ValueExt, ValueRef,
};

#[derive(Debug)]
struct Inner {
    vec: ManuallyDrop<Vec<u8>>,
    refs: Arc<NonNull<u8>>,
}

impl Inner {
    fn new(cap: usize) -> Self {
        let mut vec = vec![0u8; cap];
        let ptr = vec.as_mut_ptr();
        Self {
            vec: ManuallyDrop::new(vec),
            refs: Arc::new(unsafe { NonNull::new_unchecked(ptr) }),
        }
    }

    #[inline]
    fn copy_from(&mut self, other: &Self) {
        let len = other.vec.capacity();
        unsafe {
            core::ptr::copy_nonoverlapping(other.vec.as_ptr(), self.vec.as_mut_ptr(), len);
        }
    }
}

impl Drop for Inner {
    fn drop(&mut self) {
        if Arc::strong_count(&self.refs) == 1 {
            let cap = self.vec.capacity();
            unsafe {
                let _ = Vec::from_raw_parts(self.vec.as_mut_ptr(), cap, cap);
            }
        }
    }
}

unsafe impl Send for Inner {}
unsafe impl Sync for Inner {}
/// FixedArena should be lock-free
#[derive(Debug)]
pub(crate) struct FixedArena {
    pub(crate) n: AtomicU32,
    inner: UnsafeCell<Inner>,
}

impl FixedArena {
    #[inline]
    pub(crate) fn new(n: usize) -> Self {
        Self {
            // Don't store data at position 0 in order to reserve offset=0 as a kind
            // of nil pointer.
            inner: UnsafeCell::new(Inner::new(n.max(Node::MAX_NODE_SIZE))),
            n: AtomicU32::new(1),
        }
    }

    #[inline]
    fn allocate(&self, sz: u32) -> u32 {
        let offset = self.n.fetch_add(sz, Ordering::SeqCst) + sz;
        let inner = unsafe { &mut *self.inner.get() };
        assert!(
            (offset as usize) <= inner.vec.capacity(),
            "FixedArena: ARENA does not have enough space"
        );
        offset - sz
    }

    fn put_node(&self, height: usize) -> u32 {
        // Compute the amount of the tower that will never be used, since the height
        // is less than maxHeight.
        let unused_size = self.unused_size(height);

        // Pad the allocation with enough bytes to ensure pointer alignment.
        let l = (Node::MAX_NODE_SIZE - unused_size + Node::NODE_ALIGN) as u32;
        let n = self.allocate(l);

        // Return the aligned offset.
        let align = Node::NODE_ALIGN as u32;
        (n + align) & (!align)
    }

    pub(crate) fn put_key<'a>(&self, key: kvstructs::KeyRef<'a>) -> u32 {
        let key_size = key.len() as u32;
        let offset = self.allocate(key_size);

        let inner = unsafe { &mut *self.inner.get() };
        inner.vec[offset as usize..(offset + key_size) as usize].copy_from_slice(key.as_slice());
        offset
    }

    pub(crate) fn put_val<'a>(&self, val: kvstructs::ValueRef<'a>) -> u32 {
        let l = val.encoded_size();
        let offset = self.allocate(l);
        let inner = unsafe { &mut *self.inner.get() };
        val.encode(inner.vec[offset as usize..].as_mut());
        offset
    }

    /// Compute the amount of the tower that will never be used, since the height
    /// is less than Node::MAX_HEIGHT.
    #[inline(always)]
    fn unused_size(&self, height: usize) -> usize {
        (Node::MAX_HEIGHT - height) * Node::OFFSET_SIZE
    }

    pub(crate) fn new_node(
        &self,
        key: impl KeyExt,
        val: impl ValueExt,
        height: usize,
    ) -> *mut Node {
        let key = key.as_key_ref();
        let val = val.as_value_ref();
        let node_offset = self.put_node(height);
        let key_len = key.len();
        let key_offset = self.put_key(key);
        let v_encode_size = val.encoded_size();
        let val = Node::encode_value(self.put_val(val), v_encode_size);

        let node = unsafe { &mut *self.get_node(node_offset) };
        node.key_offset = key_offset;
        node.key_size = key_len as u16;
        node.height = height as u16;
        node.val = AtomicU64::new(val);
        node
    }

    pub(crate) fn get_node(&self, offset: u32) -> *mut Node {
        if offset == 0 {
            return core::ptr::null_mut();
        }

        let inner = unsafe { &mut *self.inner.get() };

        unsafe {
            core::mem::transmute::<*mut u8, *mut Node>(inner.vec.as_mut_ptr().add(offset as usize))
        }
    }

    pub(crate) fn get_key<'a, 'b: 'a>(&'a self, offset: u32, size: u16) -> KeyRef<'b> {
        let inner = unsafe { &*self.inner.get() };
        let size = size as u32;
        // Safety: the underlying ptr will never be freed until the Arena is dropped.
        unsafe {
            core::mem::transmute(
                RawKeyPointer::new(
                    inner.vec[offset as usize..(offset + size) as usize].as_ptr(),
                    size,
                )
                .as_key_ref(),
            )
        }
    }

    pub(crate) fn get_val<'a, 'b: 'a>(&'a self, offset: u32, size: u32) -> ValueRef<'b> {
        let inner = unsafe { &*self.inner.get() };
        // Safety: the underlying ptr will never be freed until the Arena is dropped.
        unsafe {
            core::mem::transmute(
                RawValuePointer::new(
                    inner.vec[offset as usize..(offset + size) as usize].as_ptr(),
                    size,
                )
                .as_value_ref(),
            )
        }
    }

    pub(crate) fn get_node_offset(&self, node: *const Node) -> u32 {
        if node.is_null() {
            return 0;
        }
        let inner = unsafe { &*self.inner.get() };
        node as u32 - inner.vec.as_ptr() as u32
    }

    #[inline]
    pub(crate) fn cap(&self) -> usize {
        let inner = unsafe { &*self.inner.get() };
        inner.vec.capacity()
    }

    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.n.load(Ordering::SeqCst) as usize
    }
}

unsafe impl Send for FixedArena {}
unsafe impl Sync for FixedArena {}
