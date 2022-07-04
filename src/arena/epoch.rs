use core::{alloc::Layout, mem::ManuallyDrop};

use crate::{sync::{AtomicU32, Ordering, AtomicU64, AtomicUsize}, MAX_HEIGHT, OFFSET_SIZE, NODE_ALIGN};

use crossbeam_epoch::{self as epoch, Collector, Atomic, Shared, Owned, Guard};

#[cfg(feature = "std")]
use crossbeam_epoch::default_collector;
use kvstructs::{KeyExt, ValueExt, raw_pointer::{RawKeyPointer, RawValuePointer}};

use super::growable::{MAX_NODE_SIZE, NewNode, encode_value};


pub(crate) struct Allocator {
    data: Vec<u8>,
    refs: AtomicUsize,
}

impl Allocator {
    #[inline]
    fn new(size: usize) -> Self {
        Self {
            data: alloc::vec![0; size],
            refs: AtomicUsize::new(1),
        }
    }

    #[inline]
    fn capacity(&self) -> usize {
        self.data.capacity()
    }

    #[inline]
    fn copy_from(&mut self, other: &Self) {
        let cap = other.data.capacity();
        unsafe { core::ptr::copy_nonoverlapping(other.data.as_ptr(), self.data.as_mut_ptr(), cap) }
    }



    /// Attempts to increment the reference count of a node and returns `true` on success.
    ///
    /// The reference count can be incremented only if it is non-zero.
    ///
    /// # Panics
    ///
    /// Panics if the reference count overflows.
    #[inline]
    unsafe fn try_increment(&self) -> bool {
        let mut refs = self.refs.load(Ordering::Relaxed);

        loop {
            // If the reference count is zero, then the node has already been
            // queued for deletion. Incrementing it again could lead to a
            // double-free.
            if refs == 0 {
                return false;
            }

            // If all bits in the reference count are ones, we're about to overflow it.
            let new_refs = refs
                .checked_add(1)
                .expect("SkipList reference count overflow");

            // Try incrementing the count.
            match self.refs.compare_exchange_weak(
                refs,
                new_refs,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => return true,
                Err(current) => refs = current,
            }
        }
    }

    /// Decrements the reference count of a allocator, destroying it if the count becomes zero.
    #[inline]
    unsafe fn decrement(&self, guard: &Guard) {
        if self
            .refs
            .fetch_sub(1, Ordering::Release)
            == 1
        {
            crate::sync::fence(Ordering::Acquire);
            guard.defer_unchecked(move || {
                core::ptr::drop_in_place(self.data.as_ptr() as *mut u8);
            });
        }
    }

    /// Decrements the reference count of a node, pinning the thread and destroying the node
    /// if the count become zero.
    #[inline]
    unsafe fn decrement_with_pin<F>(&self, arena: &Arena, pin: F)
    where
        F: FnOnce() -> Guard,
    {
        if self
            .refs
            .fetch_sub(1, Ordering::Release)
            == 1
        {
            crate::sync::fence(Ordering::Acquire);
            let guard = &pin();
            arena.check_guard(guard);
            guard.defer_unchecked(move || {
                core::ptr::drop_in_place(self.data.as_ptr() as *mut u8); 
            });
        }
    }
}

/// An entry in a skiplist, protected by a `Guard`.
///
/// The lifetimes of the key and value are the same as that of the `Guard`
/// used when creating the `Entry` (`'g`). This lifetime is also constrained to
/// not outlive the `SkipList`.
pub(crate) struct AllocatorEntry<'a: 'g, 'g> {
    arena: &'a Arena,
    allocator: &'g Allocator,
    guard: &'g Guard,
}

impl<'a: 'g, 'g> AllocatorEntry<'a, 'g> {
    /// Attempts to pin the entry with a reference count, ensuring that it
    /// remains accessible even after the `Guard` is dropped.
    ///
    /// This method may return `None` if the reference count is already 0 and
    /// the node has been queued for deletion.
    pub(crate) fn pin(&self) -> Option<RefAllocatorEntry<'a>> {
        unsafe { RefAllocatorEntry::try_acquire(self.arena, self.allocator) }
    }
}

impl<'a: 'g, 'g> Clone for AllocatorEntry<'a, 'g> {
    fn clone(&self) -> Self {
        Self {
            arena: self.arena,
            allocator: self.allocator,
            guard: self.guard,
        }
    }
}

pub(crate) struct RefAllocatorEntry<'a> {
    arena: &'a Arena,
    allocator: &'a Allocator,
}

impl<'a> RefAllocatorEntry<'a> {
    /// Releases the reference of the entry, pinning the thread only when
    /// the reference count of the node becomes 0.
    pub(crate) fn release_with_pin<F>(self, pin: F)
    where
        F: FnOnce() -> Guard,
    {
        unsafe { self.allocator.decrement_with_pin(self.arena, pin) }
    }

    /// Tries to create a new `RefEntry` by incrementing the reference count of
    /// a node.
    unsafe fn try_acquire(
        arena: &'a Arena,
        allocator: &Allocator,
    ) -> Option<Self> {
        if allocator.try_increment() {
            Some(Self {
                arena,
                // We re-bind the lifetime of the node here to that of the skip
                // list since we now hold a reference to it.
                allocator: &*(allocator as *const _),
            })
        } else {
            None
        }
    }
}

impl<'a> Clone for RefAllocatorEntry<'a> {
    fn clone(&self) -> Self {
        unsafe {
            // Incrementing will always succeed since we're already holding a reference to the node.
            Allocator::try_increment(self.allocator);
        }
        Self {
            arena: self.arena,
            allocator: self.allocator,
        }
    }
}


pub struct KeyEntry<'a: 'g, 'g> {
   key: RawKeyPointer,
   parent: AllocatorEntry<'a, 'g>,
}

impl<'a: 'g, 'g> KeyEntry<'a, 'g> {
    fn new(key: RawKeyPointer, parent: AllocatorEntry<'a, 'g>) -> Self {
        Self {
            key,
            parent,
        }
    }
}

impl<'a: 'g, 'g> KeyExt for KeyEntry<'a, 'g> {
    fn as_bytes(&self) -> &[u8] {
        self.key.as_bytes()
    }
}

pub struct ValueEntry<'a: 'g, 'g> {
    val: RawValuePointer,
    parent: AllocatorEntry<'a, 'g>
}

impl<'a: 'g, 'g> ValueEntry<'a, 'g> {
    fn new(val: RawValuePointer, parent: AllocatorEntry<'a, 'g>) -> Self {
        Self { val, parent }
    }

    #[inline]
    pub fn set_version(&mut self, version: u64) {
        self.val.set_version(version);
    }

    #[inline]
    pub fn get_version(&self) -> u64 {
        self.val.get_version()
    }
}

impl<'a: 'g, 'g> ValueExt for ValueEntry<'a, 'g> {
    fn parse_value(&self) -> &[u8] {
        self.val.parse_value()
    }

    fn parse_value_to_bytes(&self) -> kvstructs::bytes::Bytes {
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

pub(crate) struct Entry<'a: 'g, 'g> {
    node: *mut NewNode,
    parent: AllocatorEntry<'a, 'g>,
}

pub(crate) struct Offset<'a: 'g, 'g> {
    offset: u32,
    parent: AllocatorEntry<'a, 'g>,
}

pub struct Arena {
    pub(crate) n: AtomicU32,
    allocator: Atomic<Allocator>,
    collector: Collector,
}

impl Arena {
    #[cfg(feature = "std")]
    pub(crate) fn new(size: usize) -> Self {
        Self {
            collector: default_collector().clone(),
            n: AtomicU32::new(1),
            allocator: Atomic::new(Allocator::new(size.max(NODE_ALIGN + MAX_NODE_SIZE))),
        }
    }

    pub(crate) fn new_with_collector(size: usize, collector: Collector) -> Self {
        Self {
            n: AtomicU32::new(1),
            allocator: Atomic::new(Allocator::new(size)),
            collector,
        }
    }

    #[inline]
    fn allocate(&self, sz: u32) -> u32 {
        let offset = self.n.fetch_add(sz, Ordering::SeqCst) + sz;

        let g = &epoch::pin();
        let inner = loop {
            let shared = self.allocator.load_consume(g);
            // if tag is 1, the current buf is marked remove, we continue to get a valid buf
            if shared.tag() == 1 {
                continue;
            }
            break shared;
        };
        let allocator = unsafe { inner.deref() };

        // We are keeping extra bytes in the end so that the checkptr doesn't fail. We apply some
        // intelligence to reduce the size of the node by only keeping towers upto valid height and not
        // maxHeight. This reduces the node's size, but checkptr doesn't know about its reduced size.
        // checkptr tries to verify that the node of size MaxNodeInnerSize resides on a single heap
        // allocation which causes this error: checkptr:converted pointer straddles multiple allocations
        let cap = allocator.capacity();
        if offset as usize > cap - MAX_NODE_SIZE {
            // reallocate happens, mark inner need to be removed.
            inner.with_tag(1);

            let growby = cap.min(1 << 30).max(sz as usize);
            let mut new = Allocator::new(cap + growby);
            new.copy_from(&allocator);

            let new = Owned::new(new);

            // we actually do not care about the result, if failed, 
            // then other threads will increase the capacity for allocator successfully
            // match self.allocator.compare_exchange(inner, new.with_tag(0), Ordering::SeqCst, Ordering::Relaxed, &g) {
            //     Ok(old) => unsafe { g.defer_destroy(old); },
            //     Err(curr) => {
            //         // the current thread fail to swap new buf, destroy it immediately.
            //         unsafe { 
            //             let ug = epoch::unprotected();
            //             ug.defer_destroy(curr.new.into_shared(&ug));
            //         } 
            //     },
            // }
            let _ = self.allocator.compare_exchange(inner, new.with_tag(0), Ordering::SeqCst, Ordering::Relaxed, g);
        }

        offset - sz
    }

    fn put_node(&self, height: usize) -> u32 {
        // Compute the amount of the tower that will never be used, since the height
        // is less than maxHeight.
        let unused_size = self.unused_size(height);

        // Pad the allocation with enough bytes to ensure pointer alignment.
        let l = (MAX_NODE_SIZE - unused_size + NODE_ALIGN) as u32;
        let n = self.allocate(l);

        // Return the aligned offset.
        let align = NODE_ALIGN as u32;
        (n + align) & (!align)
    }

    pub(crate) fn put_key<'a: 'g, 'g>(&self, key: kvstructs::KeyRef<'a>, g: &'g Guard) -> u32 {
        self.check_guard(g);
        let key_size = key.len() as u32;
        let offset = self.allocate(key_size);
        let mut inner = loop {
            let curr = self.allocator.load_consume(g);
            if curr.tag() != 1 {
                break curr;
            }
        };
        let allocator = unsafe { inner.deref_mut() };
        allocator.data[offset as usize..(offset + key_size) as usize].copy_from_slice(key.as_slice());
        offset
    }

    pub(crate) fn put_val<'a: 'g, 'g>(&'a self, val: kvstructs::ValueRef<'a>, g: &'g Guard) -> u32 {
        self.check_guard(g);
        let l = val.encoded_size();
        let offset = self.allocate(l);
        let mut inner = loop {
            let curr = self.allocator.load_consume(g);
            if curr.tag() != 1 {
                break curr;
            }
        };
        let mut allocator = unsafe { inner.deref_mut() };
        val.encode(allocator.data[offset as usize..].as_mut());
        offset
    }

    /// Compute the amount of the tower that will never be used, since the height
    /// is less than MAX_HEIGHT.
    #[inline(always)]
    fn unused_size(&self, height: usize) -> usize {
        (MAX_HEIGHT - height) * OFFSET_SIZE
    }

    pub(crate) fn new_node<'a: 'g, 'g>(
        &'a self,
        key: impl KeyExt,
        val: impl ValueExt,
        height: usize,
        g: &'g Guard,
    ) -> *mut NewNode {
        self.check_guard(g);
        let key = key.as_key_ref();
        let val = val.as_value_ref();
        let node_offset = self.put_node(height);
        let key_len = key.len();
        let key_offset = self.put_key(key, g);
        let v_encode_size = val.encoded_size();
        let val = encode_value(self.put_val(val, g), v_encode_size);

        let node = unsafe { &mut *self.get_node(node_offset, g).unwrap().node };
        node.key_offset = key_offset;
        node.key_size = key_len as u16;
        node.height = height as u16;
        node.val = AtomicU64::new(val);
        node
    }

    pub(crate) fn get_node<'a: 'g, 'g>(&'a self, offset: u32, g: &'g Guard) -> Option<Entry<'a, 'g>> {
        if offset == 0 {
            return None;
        }
        self.check_guard(g);
        let mut inner = loop {
            let curr = self.allocator.load_consume(g);
            if curr.tag() != 1 {
                break curr;
            }
        };

        let allocator = unsafe { inner.deref_mut() };
        let n = unsafe {
            
            core::mem::transmute::<*mut u8, *mut NewNode>(
                allocator.data.as_mut_ptr().add(offset as usize),
            )
        };
        Some(Entry {
            node: n,
            parent: AllocatorEntry {
                arena: self,
                allocator,
                guard: g,
            },
        })
    }

    pub(crate) fn get_key<'a: 'g, 'g>(&'a self, offset: u32, size: u16, g: &'g Guard) -> KeyEntry<'a, 'g> {
        self.check_guard(g);
        let inner = loop {
            let curr = self.allocator.load_consume(g);
            if curr.tag() != 1 {
                break curr;
            }
        };

        let allocator = unsafe { inner.deref() };
        let size = size as u32;
        let kp = unsafe {
            RawKeyPointer::new(
                allocator.data[offset as usize..(offset + size) as usize].as_ptr(),
                size,
            )
        };

        KeyEntry {
            key: kp,
            parent: AllocatorEntry {
                arena: self,
                allocator,
                guard: g,
            },
        } 
    }

    pub(crate) fn get_val<'a: 'g, 'g>(&'a self, offset: u32, size: u32, g: &'g Guard) -> ValueEntry<'a, 'g> {
        self.check_guard(g);
        let inner = loop {
            let curr = self.allocator.load_consume(g);
            if curr.tag() != 1 {
                break curr;
            }
        };

        let allocator = unsafe { inner.deref() };
        let vp = unsafe {
            RawValuePointer::new(
                allocator.data[offset as usize..(offset + size) as usize].as_ptr(),
                size,
            )
        }; 
        
        ValueEntry {
            val: vp,
            parent: AllocatorEntry {
                arena: self,
                allocator,
                guard: g,
            },
        } 
    }

    pub(crate) fn get_node_offset<'a: 'g, 'g>(&'a self, node: *const NewNode, g: &'g Guard) -> Option<Offset<'a, 'g>> {
        if node.is_null() {
            return None;
        }
        let inner = loop {
            let curr = self.allocator.load_consume(g);
            if curr.tag() != 1 {
                break curr;
            }
        };

        let allocator = unsafe { inner.deref() };

        Some(Offset {
            offset: node as u32 - allocator.data.as_ptr() as u32,
            parent: AllocatorEntry {
                arena: self,
                allocator,
                guard: g,
            },
        })
    }

    #[inline]
    pub(crate) fn cap(&self) -> usize {
        let g = &epoch::pin();
        let inner = loop {
            let curr = self.allocator.load_consume(g);
            if curr.tag() != 1 {
                break curr;
            }
        }; 

        let allocator = unsafe { inner.deref() };
        allocator.capacity()
    }

    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.n.load(Ordering::SeqCst) as usize
    }

    /// Ensures that all `Guard`s used with the skip list come from the same
    /// `Collector`.
    fn check_guard(&self, guard: &Guard) {
        if let Some(c) = guard.collector() {
            assert!(c == &self.collector);
        }
    }
}

/// Helper function to retry an operation until pinning succeeds or `None` is
/// returned.
pub(crate) fn try_pin_loop<'a: 'g, 'g, F>(mut f: F) -> Option<RefAllocatorEntry<'a>>
where
    F: FnMut() -> Option<AllocatorEntry<'a, 'g>>,
{
    loop {
        if let Some(e) = f()?.pin() {
            return Some(e);
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::sync::Arc;
    use crate::utils::*;

    #[test]
    fn test_concurrent() {
        const n: usize = 1000;
        let l = Arc::new(Arena::new(10));
        let wg = Arc::new(());
        for i in 0..n {
            let w = wg.clone();
            let l = l.clone();
            std::thread::spawn(move || {
                let g = &epoch::pin();
                l.new_node(key(i), new_value(i), random_height(), g);
                drop(w);
            });
        }
        while Arc::strong_count(&wg) > 1 {}
        
    }
}