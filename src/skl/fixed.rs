use crate::skl::{Dropper, InsertResult, NoopDropper};
use crate::skl::{Node, HEIGHT_INCREASE, MAX_HEIGHT, MAX_NODE_SIZE, NODE_ALIGN, OFFSET_SIZE};
use crate::skl::fixed_arena::FixedArena;
use crate::sync::{Arc, AtomicU32, Ordering};
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
pub struct SKL<D: Dropper> {
    inner: Arc<SKLInner<D>>,
}

impl<D: Dropper> Clone for SKL<D> {
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
struct SKLInner<D: Dropper> {
    // Current height. 1 <= height <= kMaxHeight. CAS.
    hot_data: CachePadded<HotData>,
    arena: FixedArena,
    on_drop: Option<D>,
}

impl<D: Dropper> SKLInner<D> {
    #[inline]
    fn new(arena: FixedArena, dropper: Option<D>) -> Self {
        Self {
            hot_data: CachePadded::new(HotData::new(0)),
            arena,
            on_drop: dropper,
        }
    }

    #[inline]
    fn get_next(&self, nd: *const Node, height: usize) -> *const Node {
        unsafe {
            match nd.as_ref() {
                None => null(),
                Some(nd) => self.arena.get_node_ptr(nd.get_next_offset(height)),
            }
        }
    }

    #[inline]
    fn get_height(&self) -> u32 {
        self.hot_data.height.load(Ordering::SeqCst)
    }

    /// is_empty returns if the Skiplist is empty.
    #[inline]
    fn is_empty(&self) -> bool {
        unsafe { self.arena.get_head().get_next_offset(0) == 0 }
    }

    /// Push inserts the key-value pair.
    #[inline]
    fn insert_in(&self, key: Key, val: Value) -> InsertResult {
        let v = val.to_encoded().leak_data();
        // Since we allow overwrite, we may not need to create a new node. We might not even need to
        // increase the height. Let's defer these actions.
        let mut list_height = self.get_height();
        let mut prev = [null_mut(); MAX_HEIGHT + 1];
        let mut nxt = [null_mut(); MAX_HEIGHT + 1];
        prev[list_height as usize + 1] = self.arena.get_head_mut();
        nxt[list_height as usize + 1] = null_mut();

        for idx in (0..=list_height as usize).rev() {
            // Use higher level to speed up for current level.
            let (p, n) = self.find_splice_for_level(key.as_bytes(), prev[idx + 1], idx);
            prev[idx] = p;
            nxt[idx] = n;
            if p == n {
                unsafe {
                    let p_node = &mut (*p);
                    if p_node.value != v {
                        let val = replace(&mut p_node.value, v);
                        return InsertResult::Update(Value::decode_bytes( val));
                    }
                }
                return InsertResult::Equal(key, val);
            }
        }

        // We do need to create a new node.
        let height = random_height();

        let new_node_offset =
            self.arena.allocate_node(key, v, height);

        // Try to increase s.height via CAS.
        while height > list_height as usize {
            match self.hot_data.height.compare_exchange_weak(
                list_height,
                height as u32,
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                // Successfully increased skiplist.height.
                Ok(_) => break,
                Err(height) => list_height = height,
            }
        }

        let new_node = unsafe { &mut *self.arena.get_node_mut::<Node>(new_node_offset) };

        // We always insert from the base level and up. After you add a node in base level, we cannot
        // create a node in the level above because it would have discovered the node in the base level.
        for i in 0..=height {
            loop {
                if prev[i].is_null() {
                    assert!(i > 1); // This cannot happen in base level.
                    // We haven't computed prev, next for this level because height exceeds old listHeight.
                    // For these levels, we expect the lists to be sparse, so we can just search from head.
                    let (p, n) =
                        self.find_splice_for_level(&new_node.key, self.arena.get_head_mut(), i);
                    prev[i] = p;
                    nxt[i] = n;
                    // Someone adds the exact same key before we are able to do so. This can only happen on
                    // the base level. But we know we are not on the base level.
                    assert_ne!(p, n);
                }

                let nxt_offset = self.arena.get_node_offset(nxt[i]);
                new_node.tower[i].store(nxt_offset, Ordering::SeqCst);

                match unsafe { (&*prev[i]) }.tower[i].compare_exchange(
                    nxt_offset,
                    new_node_offset,
                    Ordering::SeqCst,
                    Ordering::SeqCst,
                ) {
                    Ok(_) => break,
                    Err(_) => {
                        // CAS failed. We need to recompute prev and next.
                        // It is unlikely to be helpful to try to use a different level as we redo the search,
                        // because it is unlikely that lots of nodes are inserted between prev[i] and next[i].
                        let (p, n) = self.find_splice_for_level(&new_node.key, prev[i], i);
                        if p == n {
                            assert_eq!(i, 0, "Equality can happen only on base level: {}", i);
                            unsafe {
                                let p_node = &(*p);
                                if p_node.value != new_node.value {
                                    // insertion failed, get back the key and value
                                    let key = replace(&mut new_node.key, Key::new());
                                    let val = replace(&mut new_node.value, Bytes::new());
                                    return InsertResult::Fail(key, Value::decode_bytes(val));
                                }
                                drop_in_place(new_node);
                            }
                            return InsertResult::Success;
                        }
                        prev[i] = p;
                        nxt[i] = n;
                    }
                }
            }
        }
        InsertResult::Success



    }

    /// Get gets the value associated with the key. It returns a valid value if it finds equal or earlier
    /// version of the same key.
    fn get_in(&self, key: impl KeyExt) -> Option<ValueRef> {
        let (n, _) = self.find_near(key.as_bytes(), false, true); // findGreaterOrEqual
        if n.is_null() {
            None
        } else {
            let n = unsafe { &*n };
            if !key.as_key_ref().eq(&n.key) {
                None
            } else {
                Some(ValueRef::decode_value_ref(n.value.as_ref()))
            }
        }
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

    /// Finds the node near to key.
    /// If less=true, it finds rightmost node such that node.key < key (if allowEqual=false) or
    /// node.key <= key (if allowEqual=true).
    /// If less=false, it finds leftmost node such that node.key > key (if allowEqual=false) or
    /// node.key >= key (if allowEqual=true).
    /// Returns the node found. The bool returned is true if the node has key equal to given key.
    fn find_near(&self, key: &[u8], less: bool, allow_equal: bool) -> (*const Node, bool) {
        let mut curr = self.arena.get_head_ptr();
        let mut lvl = self.get_height();
        unsafe {
            loop {
                // Assume x.key < key
                let nxt_offset = (&*curr).get_next_offset(lvl as usize);
                if nxt_offset == 0 {
                    // x.key < key < END OF LIST
                    if lvl > 0 {
                        // Can descend further to iterate closer to the end.
                        lvl -= 1;
                        continue;
                    }

                    // lvl = 0. Cannot descend further. Let's return something that makes sense.
                    if !less {
                        return (null(), false);
                    }

                    // Try to return x. Make sure it is not a head node.
                    if self.arena.is_head(curr) {
                        return (null(), false);
                    }

                    return (curr, false);
                }

                let nxt_node = self.arena.get_node_mut::<Node>(nxt_offset);
                let nxt = &*nxt_node;

                match key.cmp(&nxt.key) {
                    cmp::Ordering::Less => {
                        if lvl > 0 {
                            lvl -= 1;
                            continue;
                        }

                        // At base level. Need to return something.
                        if !less {
                            return (nxt, false);
                        }

                        // Try to return x. Make sure it is not a head node.
                        if self.arena.is_head(curr) {
                            return (null(), false);
                        }
                        return (curr, false);
                    }
                    cmp::Ordering::Equal => {
                        // x.key < key == next.key.
                        if allow_equal {
                            return (nxt, true);
                        }
                        if !less {
                            // We want >, so go to base level to grab the next bigger note.
                            let offset = nxt.get_next_offset(0);
                            return if offset == 0 {
                                (null(), false)
                            } else {
                                (self.arena.get_node_mut(offset), false)
                            };
                        }

                        // We want <. If not base level, we should go closer in the next level.
                        if lvl > 0 {
                            lvl -= 1;
                            continue;
                        }

                        // On base level. Return x.
                        if self.arena.is_head(curr) {
                            return (null(), false);
                        }
                        return (curr, false);
                    }
                    cmp::Ordering::Greater => {
                        curr = nxt_node;
                        continue;
                    }
                }
            }
        }
    }

    /// find_splice_for_level returns (outBefore, outAfter) with outBefore.key <= key <= outAfter.key.
    /// The input "before" tells us where to start looking.
    /// If we found a node with the same key, then we return outBefore = outAfter.
    /// Otherwise, outBefore.key < key < outAfter.key.
    #[cfg_attr(feature = "inline_more", inline)]
    fn find_splice_for_level(
        &self,
        key: &[u8],
        mut before: *mut Node,
        lvl: usize,
    ) -> (*mut Node, *mut Node) {
        loop {
            unsafe {
                // assume before key < key.
                let nxt_offset = (&*before).get_next_offset(lvl);
                if nxt_offset == 0 {
                    return (before, null_mut());
                }

                let nxt_ptr = self.arena.get_node_mut::<Node>(nxt_offset);
                let nxt_node = &*nxt_ptr;
                match key.cmp(&nxt_node.key) {
                    // before.key < key < next.key. We are done for this level.
                    cmp::Ordering::Less => return (before, nxt_ptr),
                    // Equality case.
                    cmp::Ordering::Equal => return (nxt_ptr, nxt_ptr),
                    // Keep moving right on this level.
                    cmp::Ordering::Greater => before = nxt_ptr,
                }
            }
        }
    }

    /// find_last returns the last element. If head (empty list), we return nil. All the find functions
    /// will NEVER return the head nodes.
    #[cfg_attr(feature = "inline_more", inline)]
    fn find_last(&self) -> *const Node {
        let mut curr = self.arena.get_head_ptr();
        let mut lvl = self.get_height();
        loop {
            let nxt = unsafe { &*curr }.get_next_offset(lvl as usize);
            if nxt != 0 {
                curr = unsafe { self.arena.get_node_mut(nxt) };
                continue;
            } else {
                if lvl == 0 {
                    if self.arena.is_head(curr) {
                        return null();
                    }
                    return curr;
                }
                lvl -= 1;
            }
        }
    }
}

impl<D: Dropper> Drop for SKLInner<D> {
    fn drop(&mut self) {
        match self.on_drop.as_mut() {
            None => {}
            Some(c) => c.on_drop(),
        }
    }
}

unsafe impl<D: Send + Dropper> Send for SKLInner<D> {}
unsafe impl<D: Send + Sync + Dropper> Sync for SKLInner<D> {}

impl SKL<NoopDropper> {
    /// Create a new skiplist according to the given capacity
    ///
    /// **Note:** The capacity stands for how many memory allocated,
    /// it does not mean the skiplist can store `cap` entries.
    pub fn new(cap: usize) -> Self {
        Self::new_with_dropper_in(cap, None)
    }
}

impl<D: Dropper> SKL<D> {
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

impl<D: Dropper> SKL<D> {
    fn new_in(arena: FixedArena, dropper: Option<D>) -> Self {
        Self {
            inner: Arc::new(SKLInner::new(arena, dropper)),
        }
    }

    /// Inserts the key-value pair.
    pub fn insert(&self, key: Key, val: Value) -> InsertResult {
        self.inner.insert_in(key, val)
    }

    /// Gets the value associated with the key. It returns a valid value if it finds equal or earlier
    /// version of the same key.
    pub fn get(&self, key: impl KeyExt) -> Option<ValueRef> {
        self.inner.get_in(key)
    }

    /// Returns a skiplist iterator.
    #[inline]
    fn iter(&self) -> SKLIterator<'_, D> {
        SKLIterator {
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
        self.inner.arena.len()
    }

    /// Returns the skiplist's capacity
    #[inline]
    pub fn cap(&self) -> usize {
        self.inner.cap()
    }

    // #[inline]
    // pub fn could_insert(&self) -> bool {
    //     self.inner.arena.could_insert()
    // }
}

impl<K: KeyExt, D: Dropper> PartialEq<K> for SKL<D> {
    fn eq(&self, other: &K) -> bool {
        match unsafe { self.inner.find_last().as_ref() } {
            None => false,
            Some(node) => node.key.eq(other),
        }
    }
}

impl<D: Dropper> PartialEq<SKL<D>> for SKL<D> {
    fn eq(&self, other: &SKL<D>) -> bool {
        match unsafe { self.inner.find_last().as_ref() } {
            None => other.inner.find_last().is_null(),
            Some(node) => match unsafe { other.inner.find_last().as_ref() } {
                None => false,
                Some(other_node) => node.key.eq(&other_node.key),
            },
        }
    }
}

impl<D: Dropper> Eq for SKL<D> {}

impl<K: KeyExt, D: Dropper> PartialOrd<K> for SKL<D> {
    fn partial_cmp(&self, other: &K) -> Option<cmp::Ordering> {
        match unsafe { self.inner.find_last().as_ref() } {
            None => None,
            Some(node) => node.key.partial_cmp(other),
        }
    }
}

impl<D: Dropper> PartialOrd<SKL<D>> for SKL<D> {
    fn partial_cmp(&self, other: &SKL<D>) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<D: Dropper> Ord for SKL<D> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        match unsafe { self.inner.find_last().as_ref() } {
            None => match unsafe { other.inner.find_last().as_ref() } {
                None => cmp::Ordering::Equal,
                Some(_) => cmp::Ordering::Greater,
            },
            Some(node) => match unsafe { other.inner.find_last().as_ref() } {
                None => cmp::Ordering::Less,
                Some(other_node) => node.key.cmp(&other_node.key),
            },
        }
    }
}

// SKLIterator is an iterator over skiplist object. For new objects, you just
// need to initialize SKLIterator.list.
#[derive(Copy, Clone, Debug)]
pub struct SKLIterator<'a, D: Dropper> {
    skl: &'a SKL<D>,
    curr: *const Node,
}

impl<'a, D: Dropper> SKLIterator<'a, D> {
    /// Key returns the key at the current position.
    #[inline]
    pub fn key(&self) -> KeyRef {
        unsafe {
            let curr = &*self.curr;
            curr.key.as_key_ref()
        }
    }

    /// Value returns value.
    #[inline]
    pub fn value(&self) -> ValueRef {
        unsafe { ValueRef::decode_value_ref(&(*self.curr).value) }
    }

    /// next advances to the next position.
    #[inline]
    pub fn next(&mut self) {
        let nxt = self.skl.inner.get_next(self.curr, 0);
        self.curr = nxt;
    }

    /// Prev advances to the previous position.
    #[inline]
    pub fn prev(&mut self) {
        let (prev, _) = self.skl.inner.find_near(self.key().as_slice(), true, false); // find <. No equality allowed.
        self.curr = prev;
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
        let tgt = self
            .skl
            .inner
            .get_next(self.skl.inner.arena.get_head_ptr(), 0);
        self.curr = tgt;
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
pub struct UniSKLIterator<'a, D: Dropper> {
    iter: SKLIterator<'a, D>,
    reversed: bool,
}

impl<'a, D: Dropper> kvstructs::iterator::Iterator for UniSKLIterator<'a, D> {
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
    fn seek<K: KeyExt>(&mut self, key: K) {
        if !self.reversed {
            self.iter.seek(key)
        } else {
            self.iter.seek_for_prev(key)
        }
    }

    #[inline]
    fn entry(&self) -> Option<(KeyRef, ValueRef)> {
        unsafe {
            match self.iter.curr.as_ref() {
                None => None,
                Some(curr) => Some((
                    curr.key.as_key_ref(),
                    ValueRef::decode_value_ref(curr.value.as_ref()),
                )),
            }
        }
    }

    /// Key returns the key at the current position.
    #[inline]
    fn key(&self) -> Option<KeyRef> {
        unsafe {
            match self.iter.curr.as_ref() {
                None => None,
                Some(curr) => Some(curr.key.as_key_ref()),
            }
        }
    }

    /// Value returns value.
    #[inline]
    fn val(&self) -> Option<ValueRef> {
        unsafe {
            match self.iter.curr.as_ref() {
                None => None,
                Some(curr) => Some(ValueRef::decode_value_ref(curr.value.as_ref())),
            }
        }
    }

    #[inline]
    fn valid(&self) -> bool {
        !self.iter.curr.is_null()
    }
}

#[cfg(feature = "std")]
#[inline]
fn random_height() -> usize {
    use rand::{thread_rng, Rng};
    let mut rng = thread_rng();
    for h in 0..(MAX_HEIGHT - 1) {
        if !rng.gen_ratio(HEIGHT_INCREASE, u32::MAX) {
            return h;
        }
    }
    MAX_HEIGHT - 1
}

#[cfg(not(feature = "std"))]
#[inline]
fn random_height() -> usize {
    let mut h = 1;
    let mh = MAX_HEIGHT as u32;
    while h < mh {
        let mut rbuf = [0; 4];
        getrandom::getrandom(rbuf.as_mut()).unwrap();
        if u32::from_ne_bytes(rbuf) <= HEIGHT_INCREASE {
            h += 1;
        } else {
            break h;
        }
    }
    h as usize
}

#[cfg(test)]
mod tests {
    use super::*;
    use kvstructs::bytes::BufMut;
    use kvstructs::{bytes::Bytes, Key, Value, ValueExt, ValueMut, ValueMutExt};
    use rand::Rng;

    const ARENA_SIZE: usize = 1 << 20;

    fn key(i: usize) -> Key {
        Key::from(format!("{:05}", i)).with_timestamp(0)
    }

    fn big_value(i: usize) -> Value {
        Value::from(format!("{:01048576}", i))
    }

    fn new_value(i: usize) -> ValueMut {
        let mut vm = ValueMut::default();
        vm.put_slice(format!("{:05}", i).as_bytes());
        vm
    }

    fn length<D: Dropper>(s: SKL<D>) -> usize {
        let mut x = s.inner.get_next(s.inner.arena.get_head_ptr(), 0);
        let mut ctr = 0;
        while !x.is_null() {
            ctr += 1;
            x = s.inner.get_next(x, 0);
        }
        ctr
    }

    #[test]
    fn test_insert() {
        let l = SKL::new(ARENA_SIZE);
        let k1 = Key::from("key1".as_bytes().to_vec()).with_timestamp(0);
        let v1 = new_value(42).freeze();
        let v1c = new_value(42).freeze();
        let ir = l.insert(k1.clone(), v1);
        assert!(matches!(ir, InsertResult::Success));
        let ir1 = l.insert(k1.clone(), v1c);
        assert!(matches!(ir1, InsertResult::Equal(..)));
        let v2 = new_value(52).freeze();
        let ir2 = l.insert(k1.clone(), v2);
        assert!(matches!(ir2, InsertResult::Update(..)));
    }

    #[test]
    fn test_basic() {
        let l = SKL::new(ARENA_SIZE);
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

    fn test_basic_large_testcases_in<D: Dropper>(l: SKL<D>) {
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
        let l = SKL::new(ARENA_SIZE);
        test_basic_large_testcases_in(l);
    }

    fn assert_find_near_not_null<D: Dropper>(
        l: SKL<D>,
        less: bool,
        allow_equal: bool,
        fk: Key,
        ek: Key,
        is_eq: bool,
    ) {
        let (n, eq) = l.inner.find_near(fk.as_slice(), less, allow_equal);
        unsafe {
            let n = &*n;
            assert!(n.key.eq(&ek));
        }
        assert_eq!(is_eq, eq);
    }

    fn assert_find_near_null<D: Dropper>(l: SKL<D>, less: bool, allow_equal: bool, fk: Key) {
        let (n, eq) = l.inner.find_near(fk.as_slice(), less, allow_equal);
        assert!(n.is_null());
        assert!(!eq);
    }

    #[test]
    fn test_find_near() {
        let l = SKL::new(ARENA_SIZE);
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
        let l = SKL::new(ARENA_SIZE);
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
            assert_eq!(new_value(i).freeze().as_value_ref(), v);
            iter.next();
        }

        assert!(!iter.valid());
    }

    // test_iter_prev tests a basic iteration over all nodes from the beginning.
    #[test]
    fn test_iter_prev() {
        let n = 100;
        let l = SKL::new(ARENA_SIZE);
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
            assert_eq!(new_value(i).freeze().as_value_ref(), v);
            iter.prev();
        }

        assert!(!iter.valid());
    }

    fn assert_seek<D: Dropper>(iter: &mut SKLIterator<D>, seek_to: &'static str) {
        iter.seek(&Key::from(seek_to).with_timestamp(0));
        assert!(iter.valid());
        assert_eq!(
            Bytes::copy_from_slice(iter.value().parse_value()),
            Bytes::from(seek_to)
        );
    }

    fn assert_seek_null<D: Dropper>(iter: &mut SKLIterator<D>, seek_to: &'static str) {
        iter.seek(&Key::from(seek_to).with_timestamp(0));
        assert!(!iter.valid());
    }

    #[test]
    fn test_iter_seek() {
        let n = 100;
        let l = SKL::new(ARENA_SIZE);
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

    fn random_key<R: Rng>(rng: &mut R) -> Key {
        let k = rng.gen::<u32>();
        let k2 = rng.gen::<u32>();
        let mut kb = k.to_le_bytes().to_vec();
        let mut k2b = k2.to_le_bytes().to_vec();
        kb.append(&mut k2b);
        Key::from(kb)
    }
}