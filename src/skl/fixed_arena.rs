use core::fmt::{Debug, Formatter};
use core::ptr::{write, write_bytes, NonNull, null, null_mut, slice_from_raw_parts};
use core::mem;
use kvstructs::bytes::Bytes;
use kvstructs::Key;
use crate::skl::{MAX_HEIGHT, MAX_NODE_SIZE, Node, NODE_ALIGN, OFFSET_SIZE};
use crate::sync::{AtomicU32, Ordering};

/// FixedArena should be lock-free
pub(crate) struct FixedArena {
    pub(crate) cap: usize,
    pub(crate) n: AtomicU32,
    buf: NonNull<u8>,
    head_offset: u32,
    head: NonNull<Node>,
}

impl FixedArena {
    #[inline]
    pub(crate) fn new(n: usize) -> Self {
        let mut buf = Vec::<u8>::with_capacity(n);
        let start_ptr = buf.as_mut_ptr();
        mem::forget(buf);

        let mut this = Self {
            // Don't store data at position 0 in order to reserve offset=0 as a kind
            // of nil pointer.
            cap: n,
            n: AtomicU32::new(1),
            buf: unsafe { NonNull::new_unchecked(start_ptr) },
            head_offset: 0,
            head: NonNull::dangling(),
        };
        let (head_offset, head_ptr) = this.allocate_head();
        this.head_offset = head_offset;
        this.head = head_ptr;
        this
    }

    #[inline]
    fn allocate(&self, sz: u32) -> u32 {
        let offset = self.n.fetch_add(sz, Ordering::SeqCst);
        assert!(
            offset + sz <= self.cap as u32,
            "SkipList: ARENA does not have enough space"
        );
        let ptr_offset = (offset as usize + NODE_ALIGN) & !NODE_ALIGN;
        ptr_offset as u32
    }

    #[inline]
    fn allocate_head(&self) -> (u32, NonNull<Node>) {
        let no = self.allocate_node(Key::new(), Bytes::new(), MAX_HEIGHT - 1);
        let head_ptr = self.get_node_mut::<Node>(no);
        unsafe { (no, NonNull::new_unchecked(head_ptr)) }
    }

    /// allocate and init node and return the node offset.
    #[inline]
    pub(crate) fn allocate_node(&self, key: Key, val: Bytes, height: usize) -> u32 {
        let sz = self.pad_allocate(height);

        let node_offset = self.allocate(sz as u32);

        self.allocate_node_helper(key, val, height, node_offset)
    }

    #[inline(always)]
    fn allocate_node_helper(
        &self,
        key: Key,
        val: Bytes,
        height: usize,
        offset: u32,
    ) -> u32 {
        unsafe {
            let node_ptr: *mut Node = self.get_node_mut(offset);
            let node = &mut *node_ptr;
            write(&mut node.key, key);
            write(&mut node.value, val);
            node.height = height as u16;
            write_bytes(node.tower.as_mut_ptr(), 0, height + 1);
        }

        offset
    }

    /// Compute the amount of the tower that will never be used, since the height
    /// is less than MAX_HEIGHT.
    #[inline(always)]
    fn unused_size(&self, height: usize) -> usize {
        (MAX_HEIGHT - height) * OFFSET_SIZE
    }

    /// Pad the allocation with enough bytes to ensure pointer alignment.
    #[inline(always)]
    fn pad_allocate(&self, height: usize) -> usize {
        MAX_NODE_SIZE + NODE_ALIGN - self.unused_size(height)
    }

    /// get_node returns a pointer to the node located at offset. If the offset is
    /// zero, then the nil node pointer is returned.
    #[inline]
    pub(crate) fn get_node_ptr<T>(&self, offset: u32) -> *const T {
        if offset == 0 {
            null()
        } else {
            unsafe { self.as_ptr().add(offset as usize) as _ }
        }
    }

    /// get_node_mut returns a pointer to the node located at offset. If the offset is
    /// zero, then the nil node pointer is returned.
    #[inline]
    pub(crate) fn get_node_mut<T>(&self, offset: u32) -> *mut T {
        if offset == 0 {
            null_mut()
        } else {
            unsafe { self.as_ptr_mut().add(offset as usize) as _ }
        }
    }

    /// get_node_offset returns the offset of node in the arena. If the node pointer is
    /// nil, then the zero offset is returned.
    #[inline]
    pub(crate) fn get_node_offset(&self, nd: *const Node) -> u32 {
        // we must make sure the address of node in the arena
        let nd_addr = nd as usize;
        let start_addr = self.as_ptr() as usize;
        let addr_range = start_addr + 1..start_addr + self.cap();

        if addr_range.contains(&nd_addr) {
            (nd_addr - start_addr) as u32
        } else {
            0
        }
    }

    #[inline]
    fn get_head_offset(&self) -> u32 {
        self.head_offset
    }

    #[inline]
    pub(crate) fn get_head(&self) -> &Node {
        unsafe { self.head.as_ref() }
    }

    #[inline]
    pub(crate) fn get_head_ptr(&self) -> *const Node {
        unsafe { self.head.as_ref() }
    }

    #[inline]
    pub(crate) fn get_head_mut(&self) -> *mut Node {
        self.head.as_ptr()
    }

    #[inline]
    pub(crate) fn is_head(&self, other: *const Node) -> bool {
        (self.head.as_ptr() as *const Node) == other
    }

    #[inline]
    fn as_ptr_mut(&self) -> *mut u8 {
        self.buf.as_ptr()
    }

    #[inline]
    fn as_ptr(&self) -> *const u8 {
        self.buf.as_ptr()
    }

    #[inline]
    pub(crate) fn cap(&self) -> usize {
        self.cap
    }

    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.n.load(Ordering::Relaxed) as usize
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
        unsafe {
            let ptr = self.buf.as_ptr();
            let cap = self.cap;
            Vec::from_raw_parts(ptr, 0, cap);
        }
    }
}

unsafe impl Send for FixedArena {}
unsafe impl Sync for FixedArena {}