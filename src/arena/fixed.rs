use crate::{
    sync::{Arc, AtomicU32, AtomicU64, Ordering},
    Node,
};
use alloc::{vec, vec::Vec};
use core::mem::{self, ManuallyDrop};
use core::ptr::{null, null_mut, slice_from_raw_parts, write, write_bytes, NonNull};
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

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(crate) struct ArenaRef {
    refs: Arc<NonNull<u8>>,
    cap: usize,
}

impl Drop for ArenaRef {
    fn drop(&mut self) {
        if Arc::strong_count(&self.refs) == 1 {
            unsafe {
                let _ = alloc::vec::Vec::from_raw_parts(self.refs.as_ptr(), self.cap, self.cap);
            }
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArcKey {
    key: RawKeyPointer,
    refs: ArenaRef,
}

impl KeyExt for ArcKey {
    fn as_bytes(&self) -> &[u8] {
        self.key.as_bytes()
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArcValue {
    val: RawValuePointer,
    refs: ArenaRef,
}

impl ArcValue {
    #[inline]
    pub(crate) fn set_version(&mut self, version: u64) {
        self.val.set_version(version)
    }

    #[inline]
    pub fn get_version(&self) -> u64 {
        self.val.get_version()
    }
}

impl ValueExt for ArcValue {
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

/// FixedArena should be lock-free
pub(crate) struct FixedArena {
    pub(crate) cap: usize,
    pub(crate) n: AtomicU32,
    buf: NonNull<u8>,
    refs: Arc<NonNull<u8>>,
}

impl FixedArena {
    #[inline]
    pub(crate) fn new(n: usize) -> Self {
        let mut buf = Vec::<u8>::with_capacity(n);
        let start_ptr = buf.as_mut_ptr();
        mem::forget(buf);
        let buf_ptr = unsafe { NonNull::new_unchecked(start_ptr) };
        Self {
            // Don't store data at position 0 in order to reserve offset=0 as a kind
            // of nil pointer.
            cap: n,
            n: AtomicU32::new(1),
            buf: buf_ptr,
            refs: Arc::new(buf_ptr),
        }
    }

    pub(crate) fn incr(&self) -> ArenaRef {
        ArenaRef {
            refs: self.refs.clone(),
            cap: self.cap,
        }
    }

    #[inline]
    fn allocate(&self, sz: u32) -> u32 {
        let offset = self.n.fetch_add(sz, Ordering::SeqCst) + sz;
        assert!(
            (offset as usize) <= self.cap,
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

        unsafe {
            let inner = self.buf.as_ptr();
            core::ptr::copy_nonoverlapping(
                key.as_ptr(),
                inner.add(offset as usize),
                key_size as usize,
            );
        }
        offset
    }

    pub(crate) fn put_val<'a>(&self, val: kvstructs::ValueRef<'a>) -> u32 {
        let l = val.encoded_size();
        let offset = self.allocate(l);
        let buf = unsafe {
            let ptr = self.buf.as_ptr();
            &mut *core::ptr::slice_from_raw_parts_mut(ptr.add(offset as usize), l as usize)
        };
        val.encode(buf);
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

        unsafe {
            core::mem::transmute::<*mut u8, *mut Node>(self.buf.as_ptr().add(offset as usize))
        }
    }

    pub(crate) fn get_key(&self, offset: u32, size: u16) -> ArcKey {
        // Safety: the underlying ptr will never be freed until the Arena is dropped.
        ArcKey {
            key: unsafe {
                RawKeyPointer::new(
                    core::ptr::slice_from_raw_parts(
                        self.buf.as_ptr().add(offset as usize),
                        size as usize,
                    ) as *const _,
                    size as u32,
                )
            },
            refs: self.incr(),
        }
    }

    pub(crate) fn get_val<'a>(&'a self, offset: u32, size: u32) -> ArcValue {
        // Safety: the underlying ptr will never be freed until the Arena is dropped.
        ArcValue {
            val: unsafe {
                RawValuePointer::new(
                    core::ptr::slice_from_raw_parts(
                        self.buf.as_ptr().add(offset as usize),
                        size as usize,
                    ) as *const _,
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
        let ptr = unsafe { self.buf.as_ptr() as u32 };
        node as u32 - ptr
    }

    #[inline]
    pub(crate) fn cap(&self) -> usize {
        self.cap
    }

    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.n.load(Ordering::SeqCst) as usize
    }
}

impl Debug for FixedArena {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        unsafe {
            f.debug_struct("FixedArena")
                .field("capacity", &self.cap)
                .field("length", &self.n.load(Ordering::SeqCst))
                .field(
                    "buf",
                    &slice_from_raw_parts(self.buf.as_ptr(), self.cap)
                        .as_ref()
                        .unwrap(),
                )
                .finish()
        }
    }
}

impl Drop for FixedArena {
    fn drop(&mut self) {
        if Arc::strong_count(&self.refs) == 1 {
            unsafe {
                let ptr = self.buf.as_ptr();
                let cap = self.cap;
                alloc::vec::Vec::from_raw_parts(ptr, 0, cap);
            }
        }
    }
}

unsafe impl Send for FixedArena {}
unsafe impl Sync for FixedArena {}
