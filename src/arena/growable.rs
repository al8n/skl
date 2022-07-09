use crate::sync::{AtomicU32, Ordering};
use crate::Node;
use alloc::rc::Rc;
use alloc::{vec, vec::Vec};
use core::cell::UnsafeCell;
use core::fmt::{Debug, Formatter};
use core::mem::{self, ManuallyDrop};
use core::ops::Deref;
use core::ptr::{null, null_mut, slice_from_raw_parts, write, write_bytes, NonNull};
use core::sync::atomic::AtomicU64;
use kvstructs::bytes::Bytes;
use kvstructs::raw_pointer::{RawKeyPointer, RawValuePointer};
use kvstructs::{KeyExt, ValueExt};

#[derive(Debug, Clone)]
pub(crate) struct ArenaRef {
    refs: Rc<NonNull<u8>>,
    cap: usize,
}

impl Drop for ArenaRef {
    fn drop(&mut self) {
        if Rc::strong_count(&self.refs) == 1 {
            unsafe {
                let _ = alloc::vec::Vec::from_raw_parts(self.refs.as_ptr(), self.cap, self.cap);
            }
        }
    }
}

pub struct RcKey {
    key: RawKeyPointer,
    refs: ArenaRef,
}

impl KeyExt for RcKey {
    fn as_bytes(&self) -> &[u8] {
        self.key.as_bytes()
    }
}

pub struct RcValue {
    val: RawValuePointer,
    refs: ArenaRef,
}

impl RcValue {
    #[inline]
    pub(crate) fn set_version(&mut self, version: u64) {
        self.val.set_version(version)
    }

    #[inline]
    pub fn get_version(&self) -> u64 {
        self.val.get_version()
    }
}

impl ValueExt for RcValue {
    fn parse_value(&self) -> &[u8] {
        self.val.parse_value()
    }

    fn parse_value_to_bytes(&self) -> Bytes {
        self.val.parse_value_to_bytes()
    }

    fn get_meta(&self) -> u8 {
        self.val.get_meta()
    }

    fn get_user_meta(&self) -> u8 {
        self.val.get_user_meta()
    }

    fn get_expires_at(&self) -> u64 {
        self.val.get_expires_at()
    }
}

#[derive(Debug)]
struct Inner {
    vec: ManuallyDrop<Vec<u8>>,
    refs: Rc<NonNull<u8>>,
}

impl Inner {
    fn new(cap: usize) -> Self {
        let mut vec = vec![0u8; cap];
        let ptr = vec.as_mut_ptr();
        Self {
            vec: ManuallyDrop::new(vec),
            refs: Rc::new(unsafe { NonNull::new_unchecked(ptr) }),
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
        if Rc::strong_count(&self.refs) == 1 {
            let cap = self.vec.capacity();
            unsafe {
                let _ = Vec::from_raw_parts(self.vec.as_mut_ptr(), cap, cap);
            }
        }
    }
}

#[derive(Debug)]
pub(crate) struct GrowableArena {
    pub(crate) n: AtomicU32,
    inner: UnsafeCell<Inner>,
}

impl GrowableArena {
    #[inline]
    pub(crate) fn new(n: usize) -> Self {
        Self {
            // Don't store data at position 0 in order to reserve offset=0 as a kind
            // of nil pointer.
            inner: UnsafeCell::new(Inner::new(n.max(Node::MAX_NODE_SIZE))),
            n: AtomicU32::new(1),
        }
    }

    pub(crate) fn incr(&self) -> ArenaRef {
        let inner = unsafe { &*self.inner.get() };
        ArenaRef {
            refs: inner.refs.clone(),
            cap: inner.vec.capacity(),
        }
    }

    #[cfg(test)]
    pub(crate) fn buf(&self) -> &[u8] {
        unsafe { &*self.inner.get() }.vec.as_slice()
    }

    #[inline]
    fn allocate(&self, sz: u32) -> u32 {
        let offset = self.n.fetch_add(sz, Ordering::SeqCst) + sz;

        let inner = unsafe { &mut *self.inner.get() };

        // We are keeping extra bytes in the end so that the checkptr doesn't fail. We apply some
        // intelligence to reduce the size of the node by only keeping towers upto valid height and not
        // maxHeight. This reduces the node's size, but checkptr doesn't know about its reduced size.
        // checkptr tries to verify that the node of size MaxNodeInnerSize resides on a single heap
        // allocation which causes this error: checkptr:converted pointer straddles multiple allocations
        let cap = inner.vec.capacity();
        if offset as usize > cap - Node::MAX_NODE_SIZE {
            let growby = cap.min(1 << 30).max(sz as usize);
            let mut new = Inner::new(cap + growby);
            new.copy_from(inner);
            *inner = new;
        }

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

    pub(crate) fn get_key(&self, offset: u32, size: u16) -> RcKey {
        let inner = unsafe { &*self.inner.get() };
        let size = size as u32;
        RcKey {
            key: unsafe {
                RawKeyPointer::new(
                    inner.vec[offset as usize..(offset + size) as usize].as_ptr(),
                    size,
                )
            },
            refs: self.incr(),
        }
    }

    pub(crate) fn get_val(&self, offset: u32, size: u32) -> RcValue {
        let inner = unsafe { &*self.inner.get() };
        RcValue {
            val: unsafe {
                RawValuePointer::new(
                    inner.vec[offset as usize..(offset + size) as usize].as_ptr(),
                    size,
                )
            },
            refs: self.incr(),
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
