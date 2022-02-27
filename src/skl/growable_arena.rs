use core::mem;
use core::ptr::NonNull;
use crossbeam_skiplist::SkipMap;
use crate::sync::AtomicUsize;
use crate::skl::fixed_arena::FixedArena;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArenaOffset {
    pub(crate) idx: usize,
    pub(crate) offset: u32,
}

impl ArenaOffset {
    #[inline]
    pub fn offset(&self) -> usize {
        self.offset as usize
    }

    #[inline]
    pub fn idx(&self) -> usize {
        self.idx
    }

    #[inline]
    pub fn is_zero(&self) -> bool {
        self.offset == 0 && self.idx == 0
    }
}


pub(crate) struct GrowableArena {
    arena: SkipMap<ArenaOffset, NonNull<u8>>,
    idx: AtomicUsize,
}

impl GrowableArena {
    pub(crate) fn allocate(&self) -> ArenaOffset {
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
    }
}