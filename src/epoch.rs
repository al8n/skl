use core::{cmp, mem::ManuallyDrop, ptr::null};

use crossbeam_epoch::{self as epoch, Guard};
use crossbeam_utils::CachePadded;
use kvstructs::{KeyExt, ValueExt};

use crate::{
    arena::epoch::{
        try_pin_value, Arena, Entry, KeyEntry as RawKeyEntry, RefKeyEntry, RefValueEntry,
        ValueEntry as RawValueEntry,
    },
    sync::{Arc, AtomicU32, Ordering},
    utils::random_height,
    Dropper, Node, NoopDropper,
};

// TODO: make this lock-free
/// Growable thread-safe ARENA based skiplist.
///
#[derive(Debug)]
#[repr(transparent)]
pub struct GrowableSKL<D: Dropper> {
    inner: Arc<parking_lot::Mutex<Inner<D>>>,
}

impl<D: Dropper> Clone for GrowableSKL<D> {
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
    arena: Arena,
    head_offset: u32,
    on_drop: Option<D>,
}

impl<D: Dropper> Inner<D> {
    #[inline]
    fn new<'g>(arena: Arena, dropper: Option<D>, g: &'g Guard) -> Self {
        let head = arena.new_node(
            kvstructs::Key::new(),
            kvstructs::Value::new(),
            Node::MAX_HEIGHT,
            g,
        );
        let ho = arena.get_node_offset(head, g).unwrap().offset;
        Self {
            hot_data: CachePadded::new(HotData::new(1)),
            arena,
            head_offset: ho,
            on_drop: dropper,
        }
    }

    #[inline]
    fn get_head<'a: 'g, 'g>(&'a self, g: &'g Guard) -> Entry<'a, 'g> {
        // Safety: head offset is not zero
        unsafe { self.arena.get_node_unchecked(self.head_offset, g) }
    }

    #[inline]
    fn get_next<'a: 'g, 'g>(
        &'a self,
        nd: *mut Node,
        height: usize,
        g: &'g Guard,
    ) -> Option<Entry<'a, 'g>> {
        unsafe {
            match nd.as_ref() {
                None => None,
                Some(node) => self.arena.get_node(node.get_next_offset(height), g),
            }
        }
    }

    // findNear finds the node near to key.
    // If less=true, it finds rightmost node such that node.key < key (if allowEqual=false) or
    // node.key <= key (if allowEqual=true).
    // If less=false, it finds leftmost node such that node.key > key (if allowEqual=false) or
    // node.key >= key (if allowEqual=true).
    // Returns the node found. The bool returned is true if the node has key equal to given key.
    fn find_near<'a: 'g, 'g>(
        &'a self,
        key: impl KeyExt,
        less: bool,
        allow_equal: bool,
        g: &'g Guard,
    ) -> (Option<Entry<'a, 'g>>, bool) {
        let key = key.as_key_ref();
        let mut curr = self.get_head(g);
        let mut level = (self.get_height() - 1) as usize;
        loop {
            // Assume curr.key < key.
            let next = self.get_next(curr.node, level, g);

            match next {
                None => {
                    // curr.key < key < END OF LIST
                    if level > 0 {
                        // Can descend further to iterate closer to the end.
                        level -= 1;
                        continue;
                    }

                    // Level=0. Cannot descend further. Let's return something that makes sense.
                    if !less {
                        return (None, false);
                    }

                    // Try to return curr. Make sure it is not a curr node.
                    if curr.node == self.get_head(g).node {
                        return (None, false);
                    }
                    return (Some(curr), false);
                }
                Some(next) => {
                    // Safety: we have checked next is not null
                    let next_ref = unsafe { &*next.node };
                    match key.compare_key(self.arena.get_key(
                        next_ref.key_offset,
                        next_ref.key_size,
                        g,
                    )) {
                        cmp::Ordering::Less => {
                            // cmp < 0. In other words, curr.key < key < next.
                            if level > 0 {
                                level -= 1;
                                continue;
                            }

                            // At base level. Need to return something.
                            if !less {
                                return (Some(next), false);
                            }

                            // Try to return curr. Make sure it is not a head node.
                            if curr.node == self.get_head(g).node {
                                return (None, false);
                            }

                            return (Some(curr), false);
                        }
                        cmp::Ordering::Equal => {
                            // curr.key < key == next.key.
                            if allow_equal {
                                return (Some(next), true);
                            }

                            if !less {
                                // We want >, so go to base level to grab the next bigger node.
                                return (self.get_next(next.node, 0, g), false);
                            }

                            // We want <. If not base level, we should go closer in the next level.
                            if level > 0 {
                                level -= 1;
                                continue;
                            }

                            // On base level. Return curr.
                            if curr.node == self.get_head(g).node {
                                return (None, false);
                            }
                            return (Some(curr), false);
                        }
                        cmp::Ordering::Greater => {
                            // curr.key < next.key < key. We can continue to move right.
                            curr = next;
                            continue;
                        }
                    }
                }
            }
        }
    }

    /// findSpliceForLevel returns (outBefore, outAfter) with outBefore.key <= key <= outAfter.key.
    /// The input "before" tells us where to start looking.
    /// If we found a node with the same key, then we return outBefore = outAfter.
    /// Otherwise, outBefore.key < key < outAfter.key.
    fn find_splice_for_level<'a: 'g, 'g>(
        &'a self,
        key: impl KeyExt,
        mut before: u32,
        level: usize,
        g: &'g Guard,
    ) -> (u32, u32) {
        let key = key.as_key_ref();
        loop {
            // Assume before.key < key.
            let before_node = unsafe { self.arena.get_node_unchecked(before, g) };
            // Safety: before is not null.
            let before_node_ref = unsafe { &*before_node.node };
            let next = before_node_ref.get_next_offset(level);
            match self.arena.get_node(next, g) {
                Some(next_node) => {
                    // Safety: we have checked next_node is not null.
                    let next_ref = unsafe { &*next_node.node };
                    let next_key = self
                        .arena
                        .get_key(next_ref.key_offset, next_ref.key_size, g);
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
                None => return (before, next),
            }
        }
    }

    fn find_last<'a: 'g, 'g>(&'a self, g: &'g Guard) -> Option<Entry<'a, 'g>> {
        let mut n = self.get_head(g);
        let mut level = self.get_height() - 1;
        loop {
            match self.get_next(n.node, level as usize, g) {
                Some(next) => {
                    n = next;
                    continue;
                }
                None => {
                    if level == 0 {
                        if n.node == self.get_head(g).node {
                            return None;
                        }
                        return Some(n);
                    }
                    level -= 1;
                }
            }
        }
    }

    #[inline]
    fn get_height(&self) -> u32 {
        self.hot_data.height.load(Ordering::SeqCst)
    }

    /// is_empty returns if the Skiplist is empty.
    #[inline]
    fn is_empty<'a: 'g, 'g>(&'a self, g: &'g Guard) -> bool {
        self.find_last(g).is_none()
    }

    /// Get gets the value associated with the key. It returns a valid value if it finds equal or earlier
    /// version of the same key.
    fn put<'a, 'g>(&'a self, key: impl KeyExt, val: impl ValueExt, g: &'g Guard) {
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
            let (prev_i, next_i) = self.find_splice_for_level(key_ref, prev[i + 1], i, g);
            prev[i] = prev_i;
            next[i] = next_i;
            // we found a node has the same key with `key`
            // hence we only update the value
            if prev_i == next_i {
                let val_offset = self.arena.put_val(val_ref, g);
                let val_encode_size = val.encoded_size();
                let encode_value = Node::encode_value(val_offset, val_encode_size);
                let prev_node = unsafe { self.arena.get_node_unchecked(prev_i, g) };
                // Safety: find_splice_for_level make sure this node ptr is not null
                let prev_node_ref = unsafe { &*prev_node.node };
                let (prev_val_offset, prev_val_size) = prev_node_ref.get_value_offset();
                let prev_val = self.arena.get_val(prev_val_offset, prev_val_size, g);
                prev_node_ref.set_val(encode_value);
                return;
            }
        }

        // We do need to create a new node.
        let height = random_height();
        let mut curr = self.arena.new_node(key_ref, val_ref, height, g);

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
                match self.arena.get_node(prev[i], g) {
                    Some(_) => {
                        curr_ref.tower[i] = AtomicU32::new(next[i]);
                        let parent_node = unsafe { self.arena.get_node_unchecked(prev[i], g) };
                        let parent_node_ref = unsafe { &*parent_node.node };
                        match parent_node_ref.tower[i].compare_exchange(
                            next[i],
                            self.arena
                                .get_node_offset(curr, g)
                                .map(|offset| offset.offset)
                                .unwrap_or(0),
                            Ordering::SeqCst,
                            Ordering::SeqCst,
                        ) {
                            // Managed to insert curr between prev[i] and next[i]. Go to the next level.
                            Ok(_) => break,
                            Err(_) => {
                                // CAS failed. We need to recompute prev and next.
                                // It is unlikely to be helpful to try to use a different level as we redo the search,
                                // because it is unlikely that lots of nodes are inserted between prev[i] and next[i].
                                let (prev_i, next_i) =
                                    self.find_splice_for_level(key_ref, prev[i], i, g);
                                prev[i] = prev_i;
                                next[i] = next_i;
                                if prev_i == next_i {
                                    assert_eq!(
                                        i, 0,
                                        "Equality can happen only on base level: {}",
                                        i
                                    );
                                    let value_offset = self.arena.put_val(val_ref, g);
                                    let encode_value_size = val_ref.encoded_size();
                                    let encode_value =
                                        Node::encode_value(value_offset, encode_value_size);
                                    let prev_node =
                                        unsafe { self.arena.get_node_unchecked(prev_i, g) };
                                    // Safety: prev_node is not null, we checked it in find_splice_for_level
                                    let prev_node_ref = unsafe { &mut *prev_node.node };
                                    prev_node_ref.set_val(encode_value);
                                    return;
                                }
                            }
                        }
                    }
                    None => {
                        assert!(i > 1); // This cannot happen in base level.
                                        // We haven't computed prev, next for this level because height exceeds old listHeight.
                                        // For these levels, we expect the lists to be sparse, so we can just search from head.
                        let (prev_i, next_i) =
                            self.find_splice_for_level(key_ref, self.head_offset, i, g);
                        prev[i] = prev_i;
                        next[i] = next_i;

                        // Someone adds the exact same key before we are able to do so. This can only happen on
                        // the base level. But we know we are not on the base level.
                        assert!(prev_i != next_i);
                    }
                }
            }
        }
    }

    fn get<'a: 'g, 'g>(&'a self, key: impl KeyExt, g: &'g Guard) -> Option<RawValueEntry<'a, 'g>> {
        let key = key.as_key_ref();

        match self.find_near(key, false, true, g) {
            (None, _) => return None,
            (Some(n), _) => {
                // Safety: we already checked n is not null.
                let n_ref = unsafe { &*n.node };
                let next_key = self.arena.get_key(n_ref.key_offset, n_ref.key_size, g);
                let timestamp = next_key.parse_timestamp();
                if !key.same_key(next_key) {
                    return None;
                }
                let (value_offset, value_size) = n_ref.get_value_offset();
                let mut vs = self.arena.get_val(value_offset, value_size, g);
                vs.set_version(timestamp);
                Some(vs)
            }
        }
    }

    /// cap returns the capacity of the Skiplist in terms of how much memory is used within its internal
    /// arena.
    #[inline]
    fn cap<'a: 'g, 'g>(&'a self, g: &'g Guard) -> usize {
        self.arena.cap(g)
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

impl GrowableSKL<NoopDropper> {
    /// Create a new skiplist according to the given capacity
    ///
    /// **Note:** The capacity stands for how many memory allocated,
    /// it does not mean the skiplist can store `cap` entries.
    pub fn new(cap: usize) -> Self {
        Self::new_with_dropper_in(cap, None)
    }
}

impl<D: Dropper> GrowableSKL<D> {
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
        let arena = Arena::new(sz);
        Self::new_in(arena, closer)
    }
}

impl<D: Dropper> GrowableSKL<D> {
    fn new_in(arena: Arena, dropper: Option<D>) -> Self {
        Self {
            inner: Arc::new(parking_lot::Mutex::new(Inner::new(
                arena,
                dropper,
                &epoch::pin(),
            ))),
        }
    }

    fn guard(&self) -> Guard {
        epoch::pin()
    }

    /// Inserts the key-value pair.
    pub fn insert(&self, key: impl KeyExt, val: impl ValueExt) {
        let inner = self.inner.lock();
        let g = &epoch::pin();
        inner.put(key, val, g)
    }

    /// Gets the value associated with the key. It returns a valid value if it finds equal or earlier
    /// version of the same key.
    pub fn get(&self, key: impl KeyExt) -> Option<ValueEntry> {
        let g = &epoch::pin();
        let key = key.as_key_ref();
        let inner = self.inner.lock();
        match inner.get(key, g) {
            Some(ent) => ent
                .pin()
                .map(|ent| ValueEntry::new(unsafe { core::mem::transmute(ent) })),
            None => None,
        }
    }

    /// Returns a skiplist iterator.
    #[inline]
    fn iter(&self) -> GrowableSKLIterator<'_, D> {
        GrowableSKLIterator {
            skl: self,
            curr: null(),
        }
    }

    /// Returns if the Skiplist is empty
    #[inline]
    pub fn is_empty(&self) -> bool {
        let inner = self.inner.lock();
        let g = &epoch::pin();
        inner.is_empty(g)
    }

    /// Returns the exact length of skiplist,
    /// this function will iterates over skiplist to give exact length
    #[inline]
    pub fn len(&self) -> usize {
        let inner = self.inner.lock();
        let g = &epoch::pin();
        let mut curr = inner.get_next(inner.get_head(g).node, 0, g);
        let mut ctr = 0;
        while let Some(val) = curr {
            ctr += 1;
            curr = inner.get_next(val.node, 0, g);
        }
        ctr
    }

    /// Returns the skiplist's capacity
    #[inline]
    pub fn cap(&self) -> usize {
        self.inner.lock().cap(&epoch::pin())
    }
}

/// GrowableSKLIterator is an iterator over skiplist object. For new objects, you just
/// need to initialize GrowableSKLIterator.list.
#[derive(Copy, Clone, Debug)]
pub struct GrowableSKLIterator<'a, D: Dropper> {
    skl: &'a GrowableSKL<D>,
    curr: *const Node,
}

impl<'a, D: Dropper> GrowableSKLIterator<'a, D> {
    /// Key returns the key at the current position.
    #[inline]
    pub fn key(&self) -> Option<KeyEntry<'a>> {
        let g = self.skl.guard();
        let curr = unsafe { &*self.curr };
        self.skl
            .inner
            .lock()
            .arena
            .get_key(curr.key_offset, curr.key_size, &g)
            .pin()
            .map(|ent| KeyEntry::new(unsafe { core::mem::transmute(ent) }))
    }

    /// Value returns value.
    #[inline]
    pub fn value(&self) -> Option<ValueEntry> {
        let g = self.skl.guard();
        let curr = unsafe { &*self.curr };
        let (value_offset, value_size) = curr.get_value_offset();
        self.skl
            .inner
            .lock()
            .arena
            .get_val(value_offset, value_size, &g)
            .pin()
            .map(|ent| ValueEntry::new(unsafe { core::mem::transmute(ent) }))
    }

    /// next advances to the next position.
    #[inline]
    pub fn next(&mut self) {
        assert!(self.valid());
        let g = self.skl.guard();
        self.curr = self
            .skl
            .inner
            .lock()
            .get_next(self.curr as *mut _, 0, &g)
            .map(|ptr| ptr.node as *const _)
            .unwrap_or(null());
    }

    /// Prev advances to the previous position.
    #[inline]
    pub fn prev(&mut self) {
        assert!(self.valid());
        let g = self.skl.guard();
        match self.key() {
            Some(key) => {
                let inner = self.skl.inner.lock();
                let (prev, _) = inner.find_near(key, true, false, &g);
                self.curr = prev.map(|ent| ent.node as *const _).unwrap_or(null());
                // find <. No equality allowed.
            }
            None => self.curr = null(),
        }
    }

    /// Seek advances to the first entry with a key >= target.
    #[inline]
    pub fn seek<K: KeyExt>(&mut self, target: K) {
        let g = self.skl.guard();
        let inner = self.skl.inner.lock();
        let (tgt, _) = inner.find_near(target.as_bytes(), false, true, &g); // find >=
        self.curr = match tgt {
            Some(ent) => ent.node,
            None => null(),
        };
    }

    /// seek_for_prev finds an entry with key <= target.
    #[inline]
    pub fn seek_for_prev<K: KeyExt>(&mut self, target: K) {
        let g = self.skl.guard();
        let inner = self.skl.inner.lock();
        let (tgt, _) = inner.find_near(target.as_bytes(), true, true, &g); // find <=
        self.curr = match tgt {
            Some(ent) => ent.node,
            None => null(),
        };
    }

    /// seek_to_first seeks position at the first entry in list.
    /// Final state of iterator is Valid() iff list is not empty.
    #[inline]
    pub fn seek_to_first(&mut self) {
        // find <=
        let inner = self.skl.inner.lock();
        let g = self.skl.guard();
        self.curr = inner
            .get_next(inner.get_head(&g).node, 0, &g)
            .map(|ent| ent.node as *const _)
            .unwrap_or(null());
    }

    /// seek_to_last seeks position at the last entry in list.
    /// Final state of iterator is Valid() iff list is not empty.
    #[inline]
    pub fn seek_to_last(&mut self) {
        let inner = self.skl.inner.lock();
        let g = self.skl.guard();
        let tgt = inner.find_last(&g);
        self.curr = match tgt {
            Some(ent) => ent.node,
            None => null(),
        };
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
pub struct UniGrowableSKLIterator<'a, D: Dropper> {
    iter: GrowableSKLIterator<'a, D>,
    reversed: bool,
}

impl<'a, D: Dropper> kvstructs::iterator::Iterator<KeyEntry<'a>, ValueEntry<'a>>
    for UniGrowableSKLIterator<'a, D>
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
    fn entry(&self) -> Option<(KeyEntry<'a>, ValueEntry<'a>)> {
        match self.iter.valid() {
            true => match (self.iter.key(), self.iter.value()) {
                (Some(key), Some(value)) => {
                    Some(unsafe { (core::mem::transmute(key), core::mem::transmute(value)) })
                }
                _ => None,
            },
            false => None,
        }
    }

    /// Key returns the key at the current position.
    #[inline]
    fn key(&self) -> Option<KeyEntry<'a>> {
        match self.valid() {
            true => self.iter.key(),
            false => None,
        }
    }

    /// Value returns value.
    #[inline]
    fn val(&self) -> Option<ValueEntry<'a>> {
        match self.valid() {
            true => unsafe { core::mem::transmute(self.iter.value()) },
            false => None,
        }
    }

    #[inline]
    fn valid(&self) -> bool {
        !self.iter.curr.is_null()
    }
}

#[derive(Debug, Clone)]
pub struct ValueEntry<'a> {
    inner: ManuallyDrop<RefValueEntry<'a>>,
}

impl<'a> ValueEntry<'a> {
    fn new(inner: RefValueEntry<'a>) -> Self {
        Self {
            inner: ManuallyDrop::new(inner),
        }
    }
}

impl<'a> ValueExt for ValueEntry<'a> {
    fn parse_value(&self) -> &[u8] {
        self.inner.parse_value()
    }

    fn parse_value_to_bytes(&self) -> kvstructs::bytes::Bytes {
        self.inner.parse_value_to_bytes()
    }

    fn get_meta(&self) -> u8 {
        self.inner.get_meta()
    }

    fn get_user_meta(&self) -> u8 {
        self.inner.get_user_meta()
    }

    fn get_expires_at(&self) -> u64 {
        self.inner.get_expires_at()
    }
}

impl Drop for ValueEntry<'_> {
    fn drop(&mut self) {
        unsafe {
            ManuallyDrop::into_inner(core::ptr::read(&self.inner)).release_with_pin(epoch::pin);
        }
    }
}

#[derive(Debug, Clone)]
pub struct KeyEntry<'a> {
    inner: ManuallyDrop<RefKeyEntry<'a>>,
}

impl<'a> KeyEntry<'a> {
    fn new(inner: RefKeyEntry<'a>) -> Self {
        Self {
            inner: ManuallyDrop::new(inner),
        }
    }
}

impl<'a> KeyExt for KeyEntry<'a> {
    fn as_bytes(&self) -> &[u8] {
        self.inner.as_bytes()
    }
}

impl Drop for KeyEntry<'_> {
    fn drop(&mut self) {
        unsafe {
            ManuallyDrop::into_inner(core::ptr::read(&self.inner)).release_with_pin(epoch::pin);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::*;
    use kvstructs::{bytes::*, *};

    const ARENA_SIZE: usize = 20;

    #[test]
    fn test_concurrent_basic() {
        const n: usize = 1000;
        let l = GrowableSKL::new(20);
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
        let l = GrowableSKL::new(20);
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

    // test_iter_next tests a basic iteration over all nodes from the beginning.
    #[test]
    fn test_iter_next() {
        let n = 100;
        let l = GrowableSKL::new(ARENA_SIZE);
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
            assert_eq!(
                new_value(i).freeze().as_value_ref(),
                v.unwrap().as_value_ref()
            );
            iter.next();
        }

        assert!(!iter.valid());
    }

    // test_iter_prev tests a basic iteration over all nodes from the beginning.
    #[test]
    fn test_iter_prev() {
        let n = 100;
        let l = GrowableSKL::new(ARENA_SIZE);
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
            assert!(iter.valid(), "{i}");
            let v = iter.value();
            assert_eq!(
                new_value(i).freeze().as_value_ref(),
                v.unwrap().as_value_ref()
            );
            iter.prev();
        }

        assert!(!iter.valid());
    }

    fn assert_seek<D: Dropper>(iter: &mut GrowableSKLIterator<D>, seek_to: &'static str) {
        iter.seek(&Key::from(seek_to).with_timestamp(0));
        assert!(iter.valid());
        assert_eq!(
            Bytes::copy_from_slice(iter.value().unwrap().parse_value()),
            Bytes::from(seek_to)
        );
    }

    fn assert_seek_null<D: Dropper>(iter: &mut GrowableSKLIterator<D>, seek_to: &'static str) {
        iter.seek(&Key::from(seek_to).with_timestamp(0));
        assert!(!iter.valid());
    }

    #[test]
    fn test_iter_seek() {
        let n = 100;
        let l = GrowableSKL::new(ARENA_SIZE);
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
            Bytes::copy_from_slice(iter.value().unwrap().parse_value()),
            Bytes::from("01000")
        );

        iter.seek(&Key::from("01000").with_timestamp(0));
        assert!(iter.valid());
        assert_eq!(
            Bytes::copy_from_slice(iter.value().unwrap().parse_value()),
            Bytes::from("01000")
        );

        iter.seek(&Key::from("01005").with_timestamp(0));
        assert!(iter.valid());
        assert_eq!(
            Bytes::copy_from_slice(iter.value().unwrap().parse_value()),
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
            Bytes::copy_from_slice(iter.value().unwrap().parse_value()),
            Bytes::from("01000")
        );

        iter.seek_for_prev(&Key::from("01005").with_timestamp(0));
        assert!(iter.valid());
        assert_eq!(
            Bytes::copy_from_slice(iter.value().unwrap().parse_value()),
            Bytes::from("01000")
        );

        iter.seek_for_prev(&Key::from("01010").with_timestamp(0));
        assert!(iter.valid());
        assert_eq!(
            Bytes::copy_from_slice(iter.value().unwrap().parse_value()),
            Bytes::from("01010")
        );

        iter.seek_for_prev(&Key::from("99999").with_timestamp(0));
        assert!(iter.valid());
        assert_eq!(
            Bytes::copy_from_slice(iter.value().unwrap().parse_value()),
            Bytes::from("01990")
        );
    }
}
