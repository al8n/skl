use super::{
  key::{Key, KeyRef},
  sync::{AtomicU32, AtomicU64, Ordering},
  value::{Value, ValueRef},
};
use core::{cmp, mem, ptr};
use crossbeam_utils::CachePadded;

mod arena;
use arena::Arena;

#[derive(Debug)]
#[repr(C, align(8))]
pub(crate) struct Node {
  // Multiple parts of the value are encoded as a single uint64 so that it
  // can be atomically loaded and stored:
  //   value offset: uint32 (bits 0-31)
  //   value size  : uint16 (bits 32-63)
  pub(crate) val: AtomicU64,

  // A byte slice is 24 bytes. We are trying to save space here.
  pub(crate) key_offset: u32, // Immutable. No need to lock to access key.
  pub(crate) key_size: u16,   // Immutable. No need to lock to access key.

  // Height of the tower.
  pub(crate) height: u8,
  // Mark the key is timestamped or not, 0 means not timestamped, 1 means timestamped.
  pub(crate) timestamped: u8,
  // Most nodes do not need to use the full height of the tower, since the
  // probability of each successive level decreases exponentially. Because
  // these elements are never accessed, they do not need to be allocated.
  // Therefore, when a node is allocated in the arena, its memory footprint
  // is deliberately truncated to not include unneeded tower elements.
  //
  // All accesses to elements should use CAS operations, with no need to lock.
  // pub(crate) tower: [crate::sync::AtomicU32; Self::MAX_HEIGHT],
}

impl Node {
  /// Always align nodes on 64-bit boundaries, even on 32-bit architectures,
  /// so that the node.value field is 64-bit aligned. This is necessary because
  /// node.getValueOffset uses atomic.LoadUint64, which expects its input
  /// pointer to be 64-bit aligned.
  const NODE_ALIGN: usize = mem::size_of::<u64>() - 1;

  /// MAX_NODE_SIZE is the memory footprint of a node of maximum height.
  const MAX_NODE_SIZE: usize =
    mem::size_of::<Self>() + Self::MAX_HEIGHT * mem::size_of::<crate::sync::AtomicU32>();

  const MAX_HEIGHT: usize = 20;

  const OFFSET_SIZE: usize = mem::size_of::<u32>();

  const HEIGHT_INCREASE: u32 = u32::MAX / 3;

  const TOWER_OFFSET: usize = mem::size_of::<AtomicU64>()
    + mem::size_of::<u32>()
    + mem::size_of::<u16>()
    + mem::size_of::<u8>()
    + mem::size_of::<u8>();

  #[inline]
  fn set_val(&self, vo: u64) {
    self.val.store(vo, Ordering::Release)
  }

  /// (val_offset, val_size)
  #[inline]
  fn get_value_offset(&self) -> (u32, u32) {
    Node::decode_value(self.val.load(Ordering::Acquire))
  }

  #[inline]
  fn get_next_offset(&self, arena: &Arena, offset: u32, height: usize) -> u32 {
    arena.tower(offset as usize, height).load(Ordering::Acquire)
  }

  #[inline]
  fn encode_value(val_offset: u32, val_size: u32) -> u64 {
    ((val_size as u64) << 32) | (val_offset as u64)
  }

  /// (val_offset, val_size)
  #[inline]
  fn decode_value(value: u64) -> (u32, u32) {
    (value as u32, (value >> 32) as u32)
  }

  #[inline]
  fn key<'a, 'b>(&'a self, arena: &'a Arena) -> KeyRef<'b> {
    arena.get_key(self.key_offset, self.key_size, self.timestamped == 1)
  }

  #[inline]
  const fn timestamped(&self) -> bool {
    self.timestamped == 1
  }
}

/// Fixed size lock-free ARENA based skiplist.
#[derive(Debug)]
pub struct SkipMap {
  // Current height. 1 <= height <= kMaxHeight. CAS.
  height: CachePadded<AtomicU32>,
  head_offset: u32,
  arena: Arena,
}

impl SkipMap {
  #[inline]
  fn get_head(&self) -> (*const Node, u32) {
    let (ptr, offset) = self.arena.get_node(self.head_offset);
    (ptr, offset)
  }

  #[inline]
  fn get_next(&self, nd: *const Node, offset: u32, height: usize) -> (*const Node, u32) {
    unsafe {
      match nd.as_ref() {
        None => (ptr::null(), 0),
        Some(nd) => {
          let (ptr, offset) = self
            .arena
            .get_node(nd.get_next_offset(&self.arena, offset, height));
          (ptr, offset)
        }
      }
    }
  }

  // findNear finds the node near to key.
  // If less=true, it finds rightmost node such that node.key < key (if allowEqual=false) or
  // node.key <= key (if allowEqual=true).
  // If less=false, it finds leftmost node such that node.key > key (if allowEqual=false) or
  // node.key >= key (if allowEqual=true).
  // Returns the node found. The bool returned is true if the node has key equal to given key.
  fn find_near(&self, key: KeyRef<'_>, less: bool, allow_equal: bool) -> (*const Node, u32, bool) {
    let (mut curr, mut curr_offset) = self.get_head();
    let mut level = (self.get_height() - 1) as usize;
    loop {
      // Assume curr.key < key.
      let (next, next_offset) = self.get_next(curr, curr_offset, level);

      if next.is_null() {
        // curr.key < key < END OF LIST
        if level > 0 {
          // Can descend further to iterate closer to the end.
          level -= 1;
          continue;
        }

        // Level=0. Cannot descend further. Let's return something that makes sense.
        if !less {
          return (ptr::null(), 0, false);
        }

        // Try to return curr. Make sure it is not a curr node.
        let (head, _) = self.get_head();
        if curr == head {
          return (ptr::null(), 0, false);
        }
        return (curr, curr_offset, false);
      }

      // Safety: we have checked next is not null
      let next_key = unsafe { (*next).key(&self.arena) };
      match key.cmp(&next_key) {
        cmp::Ordering::Less => {
          // cmp < 0. In other words, curr.key < key < next.
          if level > 0 {
            level -= 1;
            continue;
          }

          // At base level. Need to return something.
          if !less {
            return (next, next_offset, false);
          }

          // Try to return curr. Make sure it is not a head node.
          let (head, _) = self.get_head();
          if curr == head {
            return (ptr::null(), 0, false);
          }

          return (curr, curr_offset, false);
        }
        cmp::Ordering::Equal => {
          // curr.key < key == next.key.
          if allow_equal {
            return (next, next_offset, true);
          }

          if !less {
            // We want >, so go to base level to grab the next bigger node.
            let (rt, rt_offset) = self.get_next(next, next_offset, 0);
            return (rt, rt_offset, false);
          }

          // We want <. If not base level, we should go closer in the next level.
          if level > 0 {
            level -= 1;
            continue;
          }

          // On base level. Return curr.
          let (head, _) = self.get_head();
          if curr == head {
            return (ptr::null(), 0, false);
          }
          return (curr, curr_offset, false);
        }
        cmp::Ordering::Greater => {
          // curr.key < next.key < key. We can continue to move right.
          curr = next;
          curr_offset = next_offset;
          continue;
        }
      }
    }
  }

  /// findSpliceForLevel returns (outBefore, outAfter) with outBefore.key <= key <= outAfter.key.
  /// The input "before" tells us where to start looking.
  /// If we found a node with the same key, then we return outBefore = outAfter.
  /// Otherwise, outBefore.key < key < outAfter.key.
  fn find_splice_for_level(&self, key: KeyRef<'_>, mut before: u32, level: usize) -> (u32, u32) {
    unsafe {
      loop {
        // Assume before.key < key.
        let (before_node, before_node_offset) = self.arena.get_node(before);
        let next = (*before_node).get_next_offset(&self.arena, before_node_offset, level);
        let (next_node, _) = self.arena.get_node(next);
        if next_node.is_null() {
          return (before, next);
        }
        // Safety: we have checked next_node is not null.
        let next_key = (*next_node).key(&self.arena);
        match key.cmp(&next_key) {
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
  }

  fn find_last(&self) -> *const Node {
    let (mut n, mut n_offset) = self.get_head();
    let mut level = self.get_height() - 1;
    loop {
      let (next, next_offset) = self.get_next(n, n_offset, level as usize);
      if !next.is_null() {
        n = next;
        n_offset = next_offset;
        continue;
      }
      if level == 0 {
        let (head, _) = self.get_head();
        if n == head {
          return ptr::null();
        }
        return n;
      }
      level -= 1;
    }
  }

  #[inline]
  fn get_height(&self) -> u32 {
    self.height.load(Ordering::SeqCst)
  }
}

impl SkipMap {
  /// Create a new skiplist according to the given capacity
  ///
  /// **Note:** The capacity stands for how many memory allocated,
  /// it does not mean the skiplist can store `cap` entries.
  ///
  ///
  ///
  /// **What the difference between this method and [`SkipMap::mmap_anon`]?**
  ///
  /// 1. This method will use an `AlignedVec` ensures we are working within Rust's memory safety guarantees.
  ///   Even if we are working with raw pointers with `Box::into_raw`,
  ///   the backend ARENA will reclaim the ownership of this memory by converting it back to a `Box`
  ///   when dropping the backend ARENA. Since `AlignedVec` uses heap memory, the data might be more cache-friendly,
  ///   especially if you're frequently accessing or modifying it.
  ///
  /// 2. Where as [`SkipMap::mmap_anon`] will use mmap anonymous to require memory from the OS.
  ///   If you require very large contiguous memory regions, `mmap` might be more suitable because
  ///   it's more direct in requesting large chunks of memory from the OS.
  ///
  /// [`SkipMap::mmap_anon`]: #method.mmap_anon
  pub fn new(cap: usize) -> Self {
    let arena = Arena::new_vec(cap);
    let (head, _) = arena.new_node(
      Key::new().as_key_ref(),
      Value::new().as_value_ref(),
      Node::MAX_HEIGHT,
    );
    let ho = arena.get_node_offset(head);
    Self {
      height: CachePadded::new(AtomicU32::new(1)),
      arena,
      head_offset: ho,
    }
  }

  /// Create a new skipmap according to the given capacity, and mmaped to a file.
  ///
  /// **Note:** The capacity stands for how many memory mmaped,
  /// it does not mean the skipmap can store `cap` entries.
  ///
  /// `lock`: whether to lock the underlying file or not
  #[cfg(feature = "mmap")]
  #[cfg_attr(docsrs, doc(cfg(feature = "mmap")))]
  pub fn mmap(cap: usize, file: std::fs::File, lock: bool) -> std::io::Result<Self> {
    let arena = Arena::new_mmap(cap, file, lock)?;
    let (head, _) = arena.new_node(
      Key::new().as_key_ref(),
      Value::new().as_value_ref(),
      Node::MAX_HEIGHT,
    );
    let ho = arena.get_node_offset(head);
    Ok(Self {
      height: CachePadded::new(AtomicU32::new(1)),
      arena,
      head_offset: ho,
    })
  }

  /// Create a new skipmap according to the given capacity, and mmap anon.
  ///
  /// **What the difference between this method and [`SkipMap::new`]?**
  ///
  /// 1. This method will use mmap anonymous to require memory from the OS directly.
  ///   If you require very large contiguous memory regions, this method might be more suitable because
  ///   it's more direct in requesting large chunks of memory from the OS.
  ///
  /// 2. Where as [`SkipMap::new`] will use an `AlignedVec` ensures we are working within Rust's memory safety guarantees.
  ///   Even if we are working with raw pointers with `Box::into_raw`,
  ///   the backend ARENA will reclaim the ownership of this memory by converting it back to a `Box`
  ///   when dropping the backend ARENA. Since `AlignedVec` uses heap memory, the data might be more cache-friendly,
  ///   especially if you're frequently accessing or modifying it.
  ///
  /// [`SkipMap::new`]: #method.new
  #[cfg(feature = "mmap")]
  #[cfg_attr(docsrs, doc(cfg(feature = "mmap")))]
  pub fn mmap_anon(cap: usize) -> std::io::Result<Self> {
    let arena = Arena::new_anonymous_mmap(cap)?;
    let (head, _) = arena.new_node(
      Key::new().as_key_ref(),
      Value::new().as_value_ref(),
      Node::MAX_HEIGHT,
    );
    let ho = arena.get_node_offset(head);
    Ok(Self {
      height: CachePadded::new(AtomicU32::new(1)),
      arena,
      head_offset: ho,
    })
  }

  /// Inserts the key-value pair.
  pub fn insert(&self, key: Key, val: Value) {
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
        let val_encode_size = val.encoded_size() as u32;
        let encode_value = Node::encode_value(val_offset, val_encode_size);
        let (prev_node, _) = self.arena.get_node(prev_i);
        unsafe { (*prev_node).set_val(encode_value) };
        return;
      }
    }

    // We do need to create a new node.
    let height = random_height();
    let (curr, curr_offset) = self.arena.new_node(key_ref, val_ref, height);

    // Try to increase s.height via CAS.
    list_height = self.get_height();
    while height as u32 > list_height {
      match self.height.compare_exchange(
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
        if self.arena.get_node(prev[i]).0.is_null() {
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

        self
          .arena
          .tower(curr_offset as usize, i)
          .store(next[i], Ordering::Relaxed);
        let (_, parent_offset) = self.arena.get_node(prev[i]);
        match self
          .arena
          .tower(parent_offset as usize, i)
          .compare_exchange(
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
              let encode_value_size = val_ref.encoded_size() as u32;
              let encode_value = Node::encode_value(value_offset, encode_value_size);
              let (prev_node, _) = self.arena.get_node(prev_i);
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

  /// Gets the value associated with the key. It returns a valid value if it finds equal or earlier
  /// version of the same key.
  pub fn get(&self, key: KeyRef) -> Option<ValueRef> {
    let (n, _, _) = self.find_near(key, false, true); // findGreaterOrEqual.
    if n.is_null() {
      return None;
    }

    // Safety: we already checked n is not null.
    let n_ref = unsafe { &*n };
    let next_key = self
      .arena
      .get_key(n_ref.key_offset, n_ref.key_size, n_ref.timestamped());
    let timestamp = next_key.ttl();
    if key.ne(&next_key) {
      return None;
    }
    let (value_offset, value_size) = n_ref.get_value_offset();
    let mut vs = self.arena.get_val(value_offset, value_size);
    vs.version = timestamp;
    Some(vs)
  }

  /// Returns a skiplist iterator.
  #[inline]
  pub fn iter(&self) -> SkipMapIterator<'_> {
    SkipMapIterator {
      skl: self,
      curr: ptr::null(),
      curr_tower_offset: 0,
    }
  }

  /// Returns if the SkipMap is empty
  #[inline]
  pub fn is_empty(&self) -> bool {
    self.find_last().is_null()
  }

  /// Returns the length
  #[inline]
  pub fn len(&self) -> usize {
    let (head, head_offset) = self.get_head();
    let (mut x, mut x_offset) = self.get_next(head, head_offset, 0);
    let mut count = 0;
    while !x.is_null() {
      count += 1;
      (x, x_offset) = self.get_next(x, x_offset, 0);
    }
    count
  }

  /// Returns the skiplist's capacity
  #[inline]
  pub fn cap(&self) -> usize {
    self.arena.cap()
  }
}

/// SkipMapIterator is an iterator over skiplist object. For new objects, you just
/// need to initialize SkipMapIterator.list.
#[derive(Copy, Clone, Debug)]
pub struct SkipMapIterator<'a> {
  skl: &'a SkipMap,
  curr: *const Node,
  curr_tower_offset: u32,
}

impl<'a> SkipMapIterator<'a> {
  /// Key returns the key at the current position.
  #[inline]
  pub fn key<'b: 'a>(&'a self) -> KeyRef<'b> {
    unsafe {
      let curr = &*self.curr;
      self
        .skl
        .arena
        .get_key(curr.key_offset, curr.key_size, curr.timestamped())
    }
  }

  /// Value returns value.
  #[inline]
  pub fn value<'b: 'a>(&'a self) -> ValueRef<'b> {
    let curr = unsafe { &*self.curr };
    let (value_offset, value_size) = curr.get_value_offset();
    self.skl.arena.get_val(value_offset, value_size)
  }

  /// next advances to the next position.
  #[inline]
  pub fn next(&mut self) {
    assert!(self.valid());
    (self.curr, self.curr_tower_offset) = self.skl.get_next(self.curr, self.curr_tower_offset, 0);
  }

  /// Prev advances to the previous position.
  #[inline]
  pub fn prev(&mut self) {
    assert!(self.valid());
    let (prev, prev_offset, _) = self.skl.find_near(self.key(), true, false);
    self.curr = prev; // find <. No equality allowed.
    self.curr_tower_offset = prev_offset;
  }

  /// Seek advances to the first entry with a key >= target.
  #[inline]
  pub fn seek(&mut self, target: KeyRef) {
    let (tgt, tgt_offset, _) = self.skl.find_near(target, false, true); // find >=
    self.curr = tgt;
    self.curr_tower_offset = tgt_offset;
  }

  /// seek_for_prev finds an entry with key <= target.
  #[inline]
  pub fn seek_for_prev(&mut self, target: KeyRef<'_>) {
    let (tgt, tgt_offset, _) = self.skl.find_near(target, true, true); // find <=
    self.curr = tgt;
    self.curr_tower_offset = tgt_offset;
  }

  /// seek_to_first seeks position at the first entry in list.
  /// Final state of iterator is Valid() iff list is not empty.
  #[inline]
  pub fn seek_to_first(&mut self) {
    // find <=
    let (head, head_offset) = self.skl.get_head();
    (self.curr, self.curr_tower_offset) = self.skl.get_next(head, head_offset, 0);
  }

  /// seek_to_last seeks position at the last entry in list.
  /// Final state of iterator is Valid() iff list is not empty.
  #[inline]
  pub fn seek_to_last(&mut self) {
    let tgt = self.skl.find_last();
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
pub struct UniSkipMapIterator<'a> {
  iter: SkipMapIterator<'a>,
  reversed: bool,
}

impl<'a> UniSkipMapIterator<'a> {
  #[inline]
  pub fn next(&mut self) {
    if !self.reversed {
      self.iter.next()
    } else {
      self.iter.prev()
    }
  }

  #[inline]
  pub fn rewind(&mut self) {
    if !self.reversed {
      self.iter.seek_to_first()
    } else {
      self.iter.seek_to_last()
    }
  }

  #[inline]
  pub fn seek(&mut self, key: KeyRef<'_>) {
    if !self.reversed {
      self.iter.seek(key)
    } else {
      self.iter.seek_for_prev(key)
    }
  }

  #[inline]
  pub fn entry(&self) -> Option<(KeyRef<'a>, ValueRef<'a>)> {
    self
      .iter
      .valid()
      .then(|| (self.iter.key(), self.iter.value()))
  }

  /// Key returns the key at the current position.
  #[inline]
  pub fn key(&self) -> Option<KeyRef<'a>> {
    self.valid().then(|| self.iter.key())
  }

  /// Value returns value.
  #[inline]
  pub fn val(&self) -> Option<ValueRef<'a>> {
    self.valid().then(|| self.iter.value())
  }

  #[inline]
  pub fn valid(&self) -> bool {
    !self.iter.curr.is_null()
  }
}

#[cfg(test)]
mod tests;

#[cfg(feature = "std")]
#[inline]
pub(crate) fn random_height() -> usize {
  use rand::{thread_rng, Rng};
  let mut rng = thread_rng();
  for h in 1..(Node::MAX_HEIGHT - 1) {
    if !rng.gen_ratio(Node::HEIGHT_INCREASE, u32::MAX) {
      return h;
    }
  }
  Node::MAX_HEIGHT - 1
}

#[cfg(not(feature = "std"))]
#[inline]
pub(crate) fn random_height() -> usize {
  use rand::{rngs::OsRng, Rng, RngCore};

  for h in 1..(Node::MAX_HEIGHT - 1) {
    if !OsRng.gen_ratio(Node::HEIGHT_INCREASE, u32::MAX) {
      return h;
    }
  }
  Node::MAX_HEIGHT - 1
}
