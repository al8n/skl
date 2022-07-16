use super::{
    arena::fixed::FixedArena,
    sync::{Arc, AtomicU32, Ordering},
    utils::random_height,
    Dropper, InsertResult, Node, NoopDropper,
};
use core::cmp;
use core::fmt::{Debug, Formatter};
use core::mem::{self, replace};
use core::ptr::{drop_in_place, null, null_mut};
use core::ptr::{slice_from_raw_parts, write, write_bytes, NonNull};
use crossbeam_utils::CachePadded;
use kvstructs::bytes::Bytes;
use kvstructs::{Key, KeyExt, KeyRef, Value, ValueExt, ValueRef};

/// Fixed size lock-free ARENA based skiplist.
#[derive(Debug)]
#[repr(transparent)]
pub struct FixedSKL<D: Dropper> {
    inner: Arc<Inner<D>>,
}

impl<D: Dropper> Clone for FixedSKL<D> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

#[derive(Debug, Default)]
#[repr(transparent)]
struct HotData {
    height: AtomicU32,
}

impl HotData {
    const fn new(height: u32) -> Self {
        Self {
            height: AtomicU32::new(height),
        }
    }
}

#[derive(Debug)]
struct Inner<D: Dropper> {
    // Current height. 1 <= height <= kMaxHeight. CAS.
    hot_data: CachePadded<HotData>,
    head_offset: u32,
    arena: FixedArena,
    on_drop: Option<D>,
}

impl<D: Dropper> Inner<D> {
    #[inline]
    fn new(arena: FixedArena, dropper: Option<D>) -> Self {
        let head = arena.new_node(
            kvstructs::Key::new(),
            kvstructs::Value::new(),
            Node::MAX_HEIGHT,
        );
        let ho = arena.get_node_offset(head);
        Self {
            hot_data: CachePadded::new(HotData::new(1)),
            arena,
            on_drop: dropper,
            head_offset: ho,
        }
    }

    #[inline]
    fn get_head(&self) -> *const Node {
        self.arena.get_node(self.head_offset)
    }

    #[inline]
    fn get_next(&self, nd: *const Node, height: usize) -> *const Node {
        unsafe {
            match nd.as_ref() {
                None => core::ptr::null(),
                Some(nd) => self.arena.get_node(nd.get_next_offset(height)),
            }
        }
    }

    // findNear finds the node near to key.
    // If less=true, it finds rightmost node such that node.key < key (if allowEqual=false) or
    // node.key <= key (if allowEqual=true).
    // If less=false, it finds leftmost node such that node.key > key (if allowEqual=false) or
    // node.key >= key (if allowEqual=true).
    // Returns the node found. The bool returned is true if the node has key equal to given key.
    fn find_near(&self, key: impl KeyExt, less: bool, allow_equal: bool) -> (*const Node, bool) {
        let key = key.as_key_ref();
        let mut curr = self.get_head();
        let mut level = (self.get_height() - 1) as usize;
        loop {
            // Assume curr.key < key.
            let next = self.get_next(curr, level);

            if next.is_null() {
                // curr.key < key < END OF LIST
                if level > 0 {
                    // Can descend further to iterate closer to the end.
                    level -= 1;
                    continue;
                }

                // Level=0. Cannot descend further. Let's return something that makes sense.
                if !less {
                    return (null(), false);
                }

                // Try to return curr. Make sure it is not a curr node.
                if curr == self.get_head() {
                    return (null(), false);
                }
                return (curr, false);
            }

            // Safety: we have checked next is not null
            let next_ref = unsafe { &*next };
            match key.compare_key(self.arena.get_key(next_ref.key_offset, next_ref.key_size)) {
                cmp::Ordering::Less => {
                    // cmp < 0. In other words, curr.key < key < next.
                    if level > 0 {
                        level -= 1;
                        continue;
                    }

                    // At base level. Need to return something.
                    if !less {
                        return (next, false);
                    }

                    // Try to return curr. Make sure it is not a head node.
                    if curr == self.get_head() {
                        return (null(), false);
                    }

                    return (curr, false);
                }
                cmp::Ordering::Equal => {
                    // curr.key < key == next.key.
                    if allow_equal {
                        return (next, true);
                    }

                    if !less {
                        // We want >, so go to base level to grab the next bigger node.
                        return (self.get_next(next, 0), false);
                    }

                    // We want <. If not base level, we should go closer in the next level.
                    if level > 0 {
                        level -= 1;
                        continue;
                    }

                    // On base level. Return curr.
                    if curr == self.get_head() {
                        return (null(), false);
                    }
                    return (curr, false);
                }
                cmp::Ordering::Greater => {
                    // curr.key < next.key < key. We can continue to move right.
                    curr = next;
                    continue;
                }
            }
        }
    }

    /// findSpliceForLevel returns (outBefore, outAfter) with outBefore.key <= key <= outAfter.key.
    /// The input "before" tells us where to start looking.
    /// If we found a node with the same key, then we return outBefore = outAfter.
    /// Otherwise, outBefore.key < key < outAfter.key.
    fn find_splice_for_level(&self, key: impl KeyExt, mut before: u32, level: usize) -> (u32, u32) {
        let key = key.as_key_ref();
        loop {
            // Assume before.key < key.
            let before_node = self.arena.get_node(before);
            // Safety: before is not null.
            let before_node_ref = unsafe { &*before_node };
            let next = before_node_ref.get_next_offset(level);
            let next_node = self.arena.get_node(next);
            if next_node.is_null() {
                return (before, next);
            }
            // Safety: we have checked next_node is not null.
            let next_ref = unsafe { &*next_node };
            let next_key = self.arena.get_key(next_ref.key_offset, next_ref.key_size);
            match key.compare_key(next_key) {
                cmp::Ordering::Less => return (before, next),
                cmp::Ordering::Equal => return (next, next),
                cmp::Ordering::Greater => {
                    // Keep moving right on this level.
                    before = next;
                    continue;
                }
            }
        }
    }

    fn find_last(&self) -> *const Node {
        let mut n = self.get_head();
        let mut level = self.get_height() - 1;
        loop {
            let next = self.get_next(n, level as usize);
            if !next.is_null() {
                n = next;
                continue;
            }
            if level == 0 {
                if n == self.get_head() {
                    return null();
                }
                return n;
            }
            level -= 1;
        }
    }

    #[inline]
    fn get_height(&self) -> u32 {
        self.hot_data.height.load(Ordering::SeqCst)
    }

    /// is_empty returns if the Skiplist is empty.
    #[inline]
    fn is_empty(&self) -> bool {
        self.find_last().is_null()
    }

    /// Get gets the value associated with the key. It returns a valid value if it finds equal or earlier
    /// version of the same key.
    fn put(&self, key: impl KeyExt, val: impl ValueExt) {
        let key_ref = key.as_key_ref();
        let val_ref = val.as_value_ref();

        // Since we allow overwrite, we may not need to create a new node. We might not even need to
        // increase the height. Let's defer these actions.

        let mut list_height = self.get_height();
        let mut prev = [0u32; Node::MAX_HEIGHT + 1];
        let mut next = [0u32; Node::MAX_HEIGHT + 1];
        prev[list_height as usize] = self.head_offset;
        for i in (0..list_height as usize).rev() {
            // Use higher level to speed up for current level.
            let (prev_i, next_i) = self.find_splice_for_level(key_ref, prev[i + 1], i);
            prev[i] = prev_i;
            next[i] = next_i;
            // we found a node has the same key with `key`
            // hence we only update the value
            if prev_i == next_i {
                let val_offset = self.arena.put_val(val_ref);
                let val_encode_size = val.encoded_size();
                let encode_value = Node::encode_value(val_offset, val_encode_size);
                let prev_node = self.arena.get_node(prev_i);
                // Safety: find_splice_for_level make sure this node ptr is not null
                let prev_node_ref = unsafe { &*prev_node };
                let (prev_val_offset, prev_val_size) = prev_node_ref.get_value_offset();
                let prev_val = self.arena.get_val(prev_val_offset, prev_val_size);
                prev_node_ref.set_val(encode_value);
                return;
            }
        }

        // We do need to create a new node.
        let height = random_height();
        let mut curr = self.arena.new_node(key_ref, val_ref, height);

        // Safety: we just created a new node, so curr cannot be null.
        let curr_ref = unsafe { &mut *curr };

        // Try to increase s.height via CAS.
        list_height = self.get_height();
        while height as u32 > list_height {
            match self.hot_data.height.compare_exchange(
                list_height,
                height as u32,
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                // Successfully increased skiplist.height.
                Ok(_) => break,
                Err(_) => list_height = self.get_height(),
            }
        }

        // We always insert from the base level and up. After you add a node in base level, we cannot
        // create a node in the level above because it would have discovered the node in the base level.
        for i in 0..height {
            loop {
                if self.arena.get_node(prev[i]).is_null() {
                    assert!(i > 1); // This cannot happen in base level.
                                    // We haven't computed prev, next for this level because height exceeds old listHeight.
                                    // For these levels, we expect the lists to be sparse, so we can just search from head.
                    let (prev_i, next_i) = self.find_splice_for_level(key_ref, self.head_offset, i);
                    prev[i] = prev_i;
                    next[i] = next_i;

                    // Someone adds the exact same key before we are able to do so. This can only happen on
                    // the base level. But we know we are not on the base level.
                    assert!(prev_i != next_i);
                }

                curr_ref.tower[i] = AtomicU32::new(next[i]);
                let parent_node = self.arena.get_node(prev[i]);
                let parent_node_ref = unsafe { &*parent_node };
                match parent_node_ref.tower[i].compare_exchange(
                    next[i],
                    self.arena.get_node_offset(curr),
                    Ordering::SeqCst,
                    Ordering::SeqCst,
                ) {
                    // Managed to insert curr between prev[i] and next[i]. Go to the next level.
                    Ok(_) => break,
                    Err(_) => {
                        // CAS failed. We need to recompute prev and next.
                        // It is unlikely to be helpful to try to use a different level as we redo the search,
                        // because it is unlikely that lots of nodes are inserted between prev[i] and next[i].
                        let (prev_i, next_i) = self.find_splice_for_level(key_ref, prev[i], i);
                        prev[i] = prev_i;
                        next[i] = next_i;
                        if prev_i == next_i {
                            assert_eq!(i, 0, "Equality can happen only on base level: {}", i);
                            let value_offset = self.arena.put_val(val_ref);
                            let encode_value_size = val_ref.encoded_size();
                            let encode_value = Node::encode_value(value_offset, encode_value_size);
                            let prev_node = self.arena.get_node(prev_i);
                            // Safety: prev_node is not null, we checked it in find_splice_for_level
                            let prev_node_ref = unsafe { &mut *prev_node };
                            prev_node_ref.set_val(encode_value);
                            return;
                        }
                    }
                }
            }
        }
    }

    fn get(&self, key: impl KeyExt) -> Option<ValueRef> {
        let key = key.as_key_ref();
        let (n, _) = self.find_near(key, false, true); // findGreaterOrEqual.
        if n.is_null() {
            return None;
        }

        // Safety: we already checked n is not null.
        let n_ref = unsafe { &*n };
        let next_key = self.arena.get_key(n_ref.key_offset, n_ref.key_size);
        let timestamp = next_key.parse_timestamp();
        if !key.same_key(next_key) {
            return None;
        }
        let (value_offset, value_size) = n_ref.get_value_offset();
        let mut vs = self.arena.get_val(value_offset, value_size);
        vs.set_version(timestamp);
        Some(vs)
    }

    /// cap returns the capacity of the Skiplist in terms of how much memory is used within its internal
    /// arena.
    #[inline]
    fn cap(&self) -> usize {
        self.arena.cap()
    }

    /// len returns the length of the Skiplist in terms of how much memory is used within its internal
    /// arena.
    #[inline]
    fn len(&self) -> usize {
        self.arena.len()
    }
}

impl<D: Dropper> Drop for Inner<D> {
    fn drop(&mut self) {
        match self.on_drop.as_mut() {
            None => {}
            Some(c) => c.on_drop(),
        }
    }
}

unsafe impl<D: Send + Dropper> Send for Inner<D> {}
unsafe impl<D: Send + Sync + Dropper> Sync for Inner<D> {}

impl FixedSKL<NoopDropper> {
    /// Create a new skiplist according to the given capacity
    ///
    /// **Note:** The capacity stands for how many memory allocated,
    /// it does not mean the skiplist can store `cap` entries.
    pub fn new(cap: usize) -> Self {
        Self::new_with_dropper_in(cap, None)
    }
}

impl<D: Dropper> FixedSKL<D> {
    /// Create a new skiplist according to the given capacity and [`Dropper`]
    ///
    /// **Note:** The capacity stands for how many memory allocated,
    /// it does not mean the skiplist can store `cap` entries.
    ///
    /// [`Dropper`]: struct.Dropper.html
    pub fn new_with_dropper(sz: usize, closer: D) -> Self {
        Self::new_with_dropper_in(sz, Some(closer))
    }

    fn new_with_dropper_in(sz: usize, closer: Option<D>) -> Self {
        let arena = FixedArena::new(sz);
        Self::new_in(arena, closer)
    }
}

impl<D: Dropper> FixedSKL<D> {
    fn new_in(arena: FixedArena, dropper: Option<D>) -> Self {
        Self {
            inner: Arc::new(Inner::new(arena, dropper)),
        }
    }

    /// Inserts the key-value pair.
    pub fn insert(&self, key: impl KeyExt, val: impl ValueExt) {
        self.inner.put(key, val)
    }

    /// Gets the value associated with the key. It returns a valid value if it finds equal or earlier
    /// version of the same key.
    pub fn get(&self, key: impl KeyExt) -> Option<ValueRef> {
        self.inner.get(key)
    }

    /// Returns a skiplist iterator.
    #[inline]
    fn iter(&self) -> FixedSKLIterator<'_, D> {
        FixedSKLIterator {
            skl: self,
            curr: null(),
        }
    }

    /// Returns if the Skiplist is empty
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Returns the length
    #[inline]
    pub fn len(&self) -> usize {
        let mut x = self.inner.get_next(self.inner.get_head(), 0);
        let mut count = 0;
        while !x.is_null() {
            count += 1;
            x = self.inner.get_next(x, 0);
        }
        count
    }

    /// Returns the skiplist's capacity
    #[inline]
    pub fn cap(&self) -> usize {
        self.inner.cap()
    }
}

/// FixedSKLIterator is an iterator over skiplist object. For new objects, you just
/// need to initialize FixedSKLIterator.list.
#[derive(Copy, Clone, Debug)]
pub struct FixedSKLIterator<'a, D: Dropper> {
    skl: &'a FixedSKL<D>,
    curr: *const Node,
}

impl<'a, D: Dropper> FixedSKLIterator<'a, D> {
    /// Key returns the key at the current position.
    #[inline]
    pub fn key<'b: 'a>(&'a self) -> KeyRef<'b> {
        unsafe {
            let curr = &*self.curr;
            self.skl.inner.arena.get_key(curr.key_offset, curr.key_size)
        }
    }

    /// Value returns value.
    #[inline]
    pub fn value<'b: 'a>(&'a self) -> ValueRef<'b> {
        let curr = unsafe { &*self.curr };
        let (value_offset, value_size) = curr.get_value_offset();
        self.skl.inner.arena.get_val(value_offset, value_size)
    }

    /// next advances to the next position.
    #[inline]
    pub fn next(&mut self) {
        assert!(self.valid());
        self.curr = self.skl.inner.get_next(self.curr, 0);
    }

    /// Prev advances to the previous position.
    #[inline]
    pub fn prev(&mut self) {
        assert!(self.valid());
        let (prev, _) = self.skl.inner.find_near(self.key(), true, false);
        self.curr = prev; // find <. No equality allowed.
    }

    /// Seek advances to the first entry with a key >= target.
    #[inline]
    pub fn seek<K: KeyExt>(&mut self, target: K) {
        let (tgt, _) = self.skl.inner.find_near(target.as_bytes(), false, true); // find >=
        self.curr = tgt;
    }

    /// seek_for_prev finds an entry with key <= target.
    #[inline]
    pub fn seek_for_prev<K: KeyExt>(&mut self, target: K) {
        let (tgt, _) = self.skl.inner.find_near(target.as_bytes(), true, true); // find <=
        self.curr = tgt;
    }

    /// seek_to_first seeks position at the first entry in list.
    /// Final state of iterator is Valid() iff list is not empty.
    #[inline]
    pub fn seek_to_first(&mut self) {
        // find <=
        self.curr = self.skl.inner.get_next(self.skl.inner.get_head(), 0);
    }

    /// seek_to_last seeks position at the last entry in list.
    /// Final state of iterator is Valid() iff list is not empty.
    #[inline]
    pub fn seek_to_last(&mut self) {
        let tgt = self.skl.inner.find_last();
        self.curr = tgt;
    }

    /// valid returns true iff the iterator is positioned at a valid node.
    #[inline]
    pub fn valid(&self) -> bool {
        !self.curr.is_null()
    }
}

/// UniIterator is a unidirectional memtable iterator. It is a thin wrapper around
/// Iterator. We like to keep Iterator as before, because it is more powerful and
/// we might support bidirectional iterators in the future.
#[derive(Copy, Clone, Debug)]
pub struct UniFixedSKLIterator<'a, D: Dropper> {
    iter: FixedSKLIterator<'a, D>,
    reversed: bool,
}

impl<'a, D: Dropper> kvstructs::iterator::Iterator<KeyRef<'a>, ValueRef<'a>>
    for UniFixedSKLIterator<'a, D>
{
    #[inline]
    fn next(&mut self) {
        if !self.reversed {
            self.iter.next()
        } else {
            self.iter.prev()
        }
    }

    #[inline]
    fn rewind(&mut self) {
        if !self.reversed {
            self.iter.seek_to_first()
        } else {
            self.iter.seek_to_last()
        }
    }

    #[inline]
    fn seek<Q: KeyExt>(&mut self, key: Q) {
        if !self.reversed {
            self.iter.seek(key)
        } else {
            self.iter.seek_for_prev(key)
        }
    }

    #[inline]
    fn entry(&self) -> Option<(KeyRef<'a>, ValueRef<'a>)> {
        self.iter
            .valid()
            .then(|| (self.iter.key(), self.iter.value()))
    }

    /// Key returns the key at the current position.
    #[inline]
    fn key(&self) -> Option<KeyRef<'a>> {
        self.valid().then(|| self.iter.key())
    }

    /// Value returns value.
    #[inline]
    fn val(&self) -> Option<ValueRef<'a>> {
        self.valid().then(|| self.iter.value())
    }

    #[inline]
    fn valid(&self) -> bool {
        !self.iter.curr.is_null()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::*;
    use alloc::format;
    use kvstructs::bytes::BufMut;
    use kvstructs::{bytes::Bytes, Key, Value, ValueExt, ValueMut, ValueMutExt};
    use rand::Rng;

    const ARENA_SIZE: usize = 1 << 20;

    fn length<D: Dropper>(s: FixedSKL<D>) -> usize {
        let head = s.inner.get_head();
        let mut x = s.inner.get_next(head, 0);
        let mut ctr = 0;
        while !x.is_null() {
            ctr += 1;
            x = s.inner.get_next(x, 0);
        }
        ctr
    }

    #[test]
    fn test_basic() {
        let l = FixedSKL::new(ARENA_SIZE);
        let mut v1 = new_value(42);
        let mut v2 = new_value(52);
        let mut v3 = new_value(62);
        let mut v4 = new_value(72);
        let mut v5 = {
            let mut vm = ValueMut::default();
            vm.put_slice(format!("{:0102400}", 1).as_bytes());
            vm
        };

        // Have size 100 KB which is > math.MaxUint16.
        // Try inserting values.
        v1.set_meta(55);
        l.insert(
            Key::from("key1".as_bytes().to_vec()).with_timestamp(0),
            v1.freeze(),
        );

        v2.set_meta(56);
        l.insert(Key::from("key2".as_bytes()).with_timestamp(2), v2.freeze());

        v3.set_meta(57);
        l.insert(Key::from("key3".as_bytes()).with_timestamp(0), v3.freeze());

        assert!(l
            .get(&Key::from("key".as_bytes()).with_timestamp(0))
            .is_none());

        let v = l
            .get(&Key::from("key1".as_bytes()).with_timestamp(0))
            .unwrap();
        assert_eq!(v.parse_value(), "00042".as_bytes().to_vec());
        assert_eq!(v.get_meta(), 55);

        assert!(l
            .get(&Key::from("key2".as_bytes()).with_timestamp(0))
            .is_none());

        let v = l
            .get(&Key::from("key3".as_bytes()).with_timestamp(0))
            .unwrap();
        assert_eq!(v.parse_value(), "00062".as_bytes().to_vec());
        assert_eq!(v.get_meta(), 57);

        v4.set_meta(12);
        l.insert(Key::from("key3".as_bytes()).with_timestamp(1), v4.freeze());

        let v = l
            .get(&Key::from("key3".as_bytes()).with_timestamp(1))
            .unwrap();
        assert_eq!(v.parse_value(), "00072".as_bytes().to_vec());
        assert_eq!(v.get_meta(), 12);

        v5.set_meta(60);
        l.insert(
            Key::from("key4".as_bytes()).with_timestamp(1),
            v5.clone().freeze(),
        );

        let v = l
            .get(&Key::from("key4".as_bytes()).with_timestamp(1))
            .unwrap();
        assert_eq!(v.parse_value(), v5.parse_value());
        assert_eq!(v.get_meta(), 60);
    }

    fn test_basic_large_testcases_in<D: Dropper>(l: FixedSKL<D>) {
        let n = 1000;

        for i in 0..n {
            l.insert(key(i), new_value(i).freeze());
        }

        for i in 0..n {
            let v = l.get(&key(i)).unwrap();
            assert_eq!(new_value(i).parse_value(), v.parse_value());
        }

        assert_eq!(n, length(l));
    }

    #[test]
    fn test_basic_large_testcases() {
        let l = FixedSKL::new(ARENA_SIZE);
        test_basic_large_testcases_in(l);
    }

    #[test]
    fn test_concurrent_basic() {
        const n: usize = 1000;
        let l = FixedSKL::new(ARENA_SIZE);
        let wg = Arc::new(());
        for i in 0..n {
            let w = wg.clone();
            let l = l.clone();
            std::thread::spawn(move || {
                l.insert(key(i), new_value(i));
                drop(w);
            });
        }
        while Arc::strong_count(&wg) > 1 {}
        for i in 0..n {
            let w = wg.clone();
            let l = l.clone();
            std::thread::spawn(move || {
                assert_eq!(
                    l.get(key(i)).unwrap().as_value_ref(),
                    new_value(i).as_value_ref(),
                    "broken: {i}"
                );
                drop(w);
            });
        }
    }

    #[test]
    fn test_concurrent_basic_big_values() {
        const n: usize = 100;
        let l = FixedSKL::new(120 << 20);
        let wg = Arc::new(());
        for i in 0..n {
            let w = wg.clone();
            let l = l.clone();
            std::thread::spawn(move || {
                l.insert(key(i), big_value(i));
                drop(w);
            });
        }
        while Arc::strong_count(&wg) > 1 {}
        assert_eq!(n, l.len());
        for i in 0..n {
            let w = wg.clone();
            let l = l.clone();
            std::thread::spawn(move || {
                assert_eq!(
                    l.get(key(i)).unwrap().as_value_ref(),
                    big_value(i).as_value_ref(),
                    "broken: {i}"
                );
                drop(w);
            });
        }
    }

    fn assert_find_near_not_null<D: Dropper>(
        l: FixedSKL<D>,
        less: bool,
        allow_equal: bool,
        fk: Key,
        ek: Key,
        is_eq: bool,
    ) {
        let (n, eq) = l.inner.find_near(fk.as_slice(), less, allow_equal);
        unsafe {
            let n = &*n;
            let key = l.inner.arena.get_key(n.key_offset, n.key_size);
            assert!(key.same_key(&ek));
        }
        assert_eq!(is_eq, eq);
    }

    fn assert_find_near_null<D: Dropper>(l: FixedSKL<D>, less: bool, allow_equal: bool, fk: Key) {
        let (n, eq) = l.inner.find_near(fk.as_slice(), less, allow_equal);
        assert!(n.is_null());
        assert!(!eq);
    }

    #[test]
    fn test_find_near() {
        let l = FixedSKL::new(ARENA_SIZE);
        for i in 0..1000 {
            let k = Key::from(format!("{:05}", i * 10 + 5)).with_timestamp(0);
            l.insert(k, new_value(i).freeze());
        }

        assert_find_near_not_null(
            l.clone(),
            false,
            false,
            Key::from("00001").with_timestamp(0),
            Key::from("00005").with_timestamp(0),
            false,
        );

        assert_find_near_not_null(
            l.clone(),
            false,
            true,
            Key::from("00001").with_timestamp(0),
            Key::from("00005").with_timestamp(0),
            false,
        );

        assert_find_near_null(l.clone(), true, false, Key::from("00001").with_timestamp(0));

        assert_find_near_null(l.clone(), true, true, Key::from("00001").with_timestamp(0));

        assert_find_near_not_null(
            l.clone(),
            false,
            false,
            Key::from("00005").with_timestamp(0),
            Key::from("00015").with_timestamp(0),
            false,
        );

        assert_find_near_not_null(
            l.clone(),
            false,
            true,
            Key::from("00005").with_timestamp(0),
            Key::from("00005").with_timestamp(0),
            true,
        );

        assert_find_near_null(l.clone(), true, false, Key::from("00005").with_timestamp(0));

        assert_find_near_not_null(
            l.clone(),
            true,
            true,
            Key::from("00005").with_timestamp(0),
            Key::from("00005").with_timestamp(0),
            true,
        );

        assert_find_near_not_null(
            l.clone(),
            false,
            false,
            Key::from("05555").with_timestamp(0),
            Key::from("05565").with_timestamp(0),
            false,
        );

        assert_find_near_not_null(
            l.clone(),
            false,
            true,
            Key::from("05555").with_timestamp(0),
            Key::from("05555").with_timestamp(0),
            true,
        );

        assert_find_near_not_null(
            l.clone(),
            true,
            false,
            Key::from("05555").with_timestamp(0),
            Key::from("05545").with_timestamp(0),
            false,
        );

        assert_find_near_not_null(
            l.clone(),
            true,
            true,
            Key::from("05555").with_timestamp(0),
            Key::from("05555").with_timestamp(0),
            true,
        );

        assert_find_near_not_null(
            l.clone(),
            false,
            false,
            Key::from("05558").with_timestamp(0),
            Key::from("05565").with_timestamp(0),
            false,
        );

        assert_find_near_not_null(
            l.clone(),
            false,
            true,
            Key::from("05558").with_timestamp(0),
            Key::from("05565").with_timestamp(0),
            false,
        );

        assert_find_near_not_null(
            l.clone(),
            true,
            false,
            Key::from("05558").with_timestamp(0),
            Key::from("05555").with_timestamp(0),
            false,
        );

        assert_find_near_not_null(
            l.clone(),
            true,
            true,
            Key::from("05558").with_timestamp(0),
            Key::from("05555").with_timestamp(0),
            false,
        );

        assert_find_near_null(
            l.clone(),
            false,
            false,
            Key::from("09995").with_timestamp(0),
        );

        assert_find_near_not_null(
            l.clone(),
            false,
            true,
            Key::from("09995").with_timestamp(0),
            Key::from("09995").with_timestamp(0),
            true,
        );

        assert_find_near_not_null(
            l.clone(),
            true,
            false,
            Key::from("09995").with_timestamp(0),
            Key::from("09985").with_timestamp(0),
            false,
        );

        assert_find_near_not_null(
            l.clone(),
            true,
            false,
            Key::from("09995").with_timestamp(0),
            Key::from("09985").with_timestamp(0),
            false,
        );

        assert_find_near_null(
            l.clone(),
            false,
            false,
            Key::from("59995").with_timestamp(0),
        );

        assert_find_near_null(l.clone(), false, true, Key::from("59995").with_timestamp(0));

        assert_find_near_not_null(
            l.clone(),
            true,
            false,
            Key::from("59995").with_timestamp(0),
            Key::from("09995").with_timestamp(0),
            false,
        );

        assert_find_near_not_null(
            l.clone(),
            true,
            true,
            Key::from("59995").with_timestamp(0),
            Key::from("09995").with_timestamp(0),
            false,
        );
    }

    // test_iter_next tests a basic iteration over all nodes from the beginning.
    #[test]
    fn test_iter_next() {
        let n = 100;
        let l = FixedSKL::new(ARENA_SIZE);
        let mut iter = l.iter();
        assert!(!iter.valid());
        iter.seek_to_first();
        assert!(!iter.valid());
        for i in (0..n).rev() {
            l.insert(
                Key::from(format!("{:05}", i)).with_timestamp(0),
                new_value(i).freeze(),
            );
        }
        iter.seek_to_first();
        for i in 0..n {
            assert!(iter.valid());
            let v = iter.value();
            assert_eq!(new_value(i).freeze().as_value_ref(), v.as_value_ref());
            iter.next();
        }

        assert!(!iter.valid());
    }

    // test_iter_prev tests a basic iteration over all nodes from the beginning.
    #[test]
    fn test_iter_prev() {
        let n = 100;
        let l = FixedSKL::new(ARENA_SIZE);
        let mut iter = l.iter();
        assert!(!iter.valid());
        iter.seek_to_first();
        assert!(!iter.valid());
        for i in 0..n {
            l.insert(
                Key::from(format!("{:05}", i)).with_timestamp(0),
                new_value(i).freeze(),
            );
        }

        iter.seek_to_last();
        for i in (0..n).rev() {
            assert!(iter.valid());
            let v = iter.value();
            assert_eq!(new_value(i).freeze().as_value_ref(), v.as_value_ref());
            iter.prev();
        }

        assert!(!iter.valid());
    }

    fn assert_seek<D: Dropper>(iter: &mut FixedSKLIterator<D>, seek_to: &'static str) {
        iter.seek(&Key::from(seek_to).with_timestamp(0));
        assert!(iter.valid());
        assert_eq!(
            Bytes::copy_from_slice(iter.value().parse_value()),
            Bytes::from(seek_to)
        );
    }

    fn assert_seek_null<D: Dropper>(iter: &mut FixedSKLIterator<D>, seek_to: &'static str) {
        iter.seek(&Key::from(seek_to).with_timestamp(0));
        assert!(!iter.valid());
    }

    #[test]
    fn test_iter_seek() {
        let n = 100;
        let l = FixedSKL::new(ARENA_SIZE);
        let mut iter = l.iter();
        assert!(!iter.valid());
        iter.seek_to_first();
        assert!(!iter.valid());

        for i in (0..n).rev() {
            let v = i * 10 + 1000;
            l.insert(
                Key::from(format!("{:05}", v)).with_timestamp(0),
                new_value(v).freeze(),
            );
        }

        iter.seek_to_first();
        assert!(iter.valid());
        assert_eq!(
            Bytes::copy_from_slice(iter.value().parse_value()),
            Bytes::from("01000")
        );

        iter.seek(&Key::from("01000").with_timestamp(0));
        assert!(iter.valid());
        assert_eq!(
            Bytes::copy_from_slice(iter.value().parse_value()),
            Bytes::from("01000")
        );

        iter.seek(&Key::from("01005").with_timestamp(0));
        assert!(iter.valid());
        assert_eq!(
            Bytes::copy_from_slice(iter.value().parse_value()),
            Bytes::from("01010")
        );

        assert_seek(&mut iter, "01010");
        assert_seek_null(&mut iter, "99999");

        // Try seek for prev
        iter.seek_for_prev(&Key::from("00").with_timestamp(0));
        assert!(!iter.valid());

        iter.seek_for_prev(&Key::from("01000").with_timestamp(0));
        assert!(iter.valid());
        assert_eq!(
            Bytes::copy_from_slice(iter.value().parse_value()),
            Bytes::from("01000")
        );

        iter.seek_for_prev(&Key::from("01005").with_timestamp(0));
        assert!(iter.valid());
        assert_eq!(
            Bytes::copy_from_slice(iter.value().parse_value()),
            Bytes::from("01000")
        );

        iter.seek_for_prev(&Key::from("01010").with_timestamp(0));
        assert!(iter.valid());
        assert_eq!(
            Bytes::copy_from_slice(iter.value().parse_value()),
            Bytes::from("01010")
        );

        iter.seek_for_prev(&Key::from("99999").with_timestamp(0));
        assert!(iter.valid());
        assert_eq!(
            Bytes::copy_from_slice(iter.value().parse_value()),
            Bytes::from("01990")
        );
    }
}
