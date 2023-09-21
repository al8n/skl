use core::{
  borrow::{Borrow, BorrowMut},
  cmp, ptr,
};

use crossbeam_utils::CachePadded;

use crate::{
  error::Error,
  sync::{AtomicU32, Ordering},
  Comparator, Key, KeyRef, Value, ValueRef, NODE_ALIGNMENT_FACTOR,
};

mod arena;
use arena::Arena;
mod node;
use node::Node;

use self::node::NodePtr;

const MAX_HEIGHT: usize = 20;

/// Precompute the skiplist probabilities so that only a single random number
/// needs to be generated and so that the optimal pvalue can be used (inverse
/// of Euler's number).
const PROBABILITIES: [u32; MAX_HEIGHT] = {
  const P: f64 = 1.0 / core::f64::consts::E;

  let mut probabilities = [0; MAX_HEIGHT];
  let mut p = 1f64;

  let mut i = 0;
  while i < MAX_HEIGHT {
    probabilities[i] = ((u32::MAX as f64) * p) as u32;
    p *= P;
    i += 1;
  }

  probabilities
};

/// A fast, cocnurrent map implementation based on skiplist that supports forward
/// and backward iteration. Keys and values are immutable once added to the skipmap and
/// deletion is not supported. Instead, higher-level code is expected to add new
/// entries that shadow existing entries and perform deletion via tombstones. It
/// is up to the user to process these shadow entries and tombstones
/// appropriately during retrieval.
#[derive(Debug)]
pub struct SkipMap<K: Key, V: Value, C: Comparator = ()> {
  arena: Arena,
  head: NodePtr<K::Trailer, V::Trailer>,
  tail: NodePtr<K::Trailer, V::Trailer>,

  /// Current height. 1 <= height <= kMaxHeight. CAS.
  height: CachePadded<AtomicU32>,

  /// If set to true by tests, then extra delays are added to make it easier to
  /// detect unusual race conditions.
  #[cfg(test)]
  testing: bool,

  cmp: C,
}

// --------------------------------Public Methods--------------------------------
impl<K: Key, V: Value, C: Comparator> SkipMap<K, V, C> {
  /// Returns the height of the highest tower within any of the nodes that
  /// have ever been allocated as part of this skiplist.
  #[inline]
  pub fn height(&self) -> u32 {
    self.height.load(Ordering::Acquire)
  }

  /// Returns the arena backing this skipmap.
  #[inline]
  pub fn arena(&self) -> &Arena {
    &self.arena
  }

  /// Returns the number of bytes that have allocated from the arena.
  #[inline]
  pub fn size(&self) -> usize {
    self.arena.size()
  }
}

impl<K: Key, V: Value> SkipMap<K, V> {
  pub fn new(cap: usize) -> Self {
    assert!(((core::mem::align_of::<K::Trailer>() % NODE_ALIGNMENT_FACTOR) == 0) || (core::mem::size_of::<K::Trailer>() == 0), "Invalid Trailer type of key, the alignment of the types implement Trailer trait must be a multiple of 4 or (ZST) zero sized type.");
    assert!(((core::mem::align_of::<V::Trailer>() % NODE_ALIGNMENT_FACTOR) == 0) || (core::mem::size_of::<V::Trailer>() == 0), "Invalid Trailer type of value, the alignment of the types implement Trailer trait must be a multiple of 4 or (ZST) zero sized type.");
    todo!()
  }
}

impl<K: Key, V: Value, C: Comparator> SkipMap<K, V, C> {
  /// Returns true if the key exists in the map.
  #[inline]
  pub fn contains_key<'a: 'b, 'b, Q>(&'b self, key: &'a Q) -> bool
  where
    K::Trailer: 'b,
    V::Trailer: 'b,
    Q: Ord + ?Sized + Borrow<KeyRef<'b, K>>,
  {
    unsafe {
      self
        .find_splice(key.borrow(), &mut Default::default(), true)
        .0
    }
  }

  /// Returns the value associated with the given key, if it exists.
  pub fn get<'a: 'b, 'b, Q>(&'b self, key: &'a Q) -> Option<ValueRef<'b, V>>
  where
    K::Trailer: 'b,
    V::Trailer: 'b,
    Q: Ord + ?Sized + Borrow<KeyRef<'b, K>>,
  {
    let key = key.borrow();
    let (n, _) = unsafe { self.find_near(key.borrow(), false, true) }; // findGreaterOrEqual.
    if n.is_null() {
      return None;
    }

    // Safety: we already checked n is not null.
    unsafe {
      let nd = n.as_ptr();
      let next_key = nd.get_key(&self.arena);
      if key.as_bytes().ne(next_key) {
        return None;
      }
      Some(ValueRef::new(nd.get_value(&self.arena), nd.value_trailer))
    }
  }

  /// Gets or inserts a new entry.
  ///
  /// # Success
  ///
  /// - Returns `Ok(Some(&[u8]))` if the key exists.
  /// - Returns `Ok(None)` if the key does not exist, and successfully inserts the key and value.
  ///
  /// As a low-level crate, users are expected to handle the error cases themselves.
  ///
  /// # Errors
  ///
  /// - Returns `Err(Error::Duplicated)`, if the key already exists.
  /// - Returns `Err(Error::Full)`, if there isn't enough room in the arena.
  pub fn get_or_insert<'a: 'b, 'b, Q, R>(
    &'b self,
    key: &'a Q,
    value: &'a R,
  ) -> Result<Option<ValueRef<'b, V>>, Error>
  where
    K::Trailer: 'b,
    V::Trailer: 'b,
    Q: Ord + ?Sized + Borrow<KeyRef<'b, K>>,
    R: Borrow<ValueRef<'a, V>> + ?Sized,
  {
    let key = key.borrow();
    let val = value.borrow();
    let ins = &mut Default::default();

    unsafe {
      let (_, curr) = self.find_splice(key.borrow(), ins, true);
      if let Some(curr) = curr {
        return Ok(Some({
          let nd = curr.as_ptr();
          ValueRef::new(nd.get_value(&self.arena), nd.value_trailer)
        }));
      }
      self.insert_in(key, val, ins).map(|_| None)
    }
  }

  /// Inserts a new key if it does not yet exist. Returns `Ok(())` if the key was successfully inserted.
  ///
  /// As a low-level crate, users are expected to handle the error cases themselves.
  ///
  /// # Errors
  ///
  /// - Returns `Error::Duplicated`, if the key already exists.
  /// - Returns `Error::Full`, if there isn't enough room in the arena.
  pub fn insert<'a, Q, R>(&'a self, key: &'a Q, value: &'a R) -> Result<(), Error>
  where
    K::Trailer: 'a,
    V::Trailer: 'a,
    Q: Ord + ?Sized + Borrow<KeyRef<'a, K>>,
    R: Borrow<ValueRef<'a, V>> + ?Sized,
  {
    // let mut x = std::collections::BTreeMap::new();
    // x.get(key)
    self.insert_in(key.borrow(), value.borrow(), &mut Inserter::default())
  }
}

impl<K: Key, V: Value, C: Comparator> SkipMap<K, V, C> {
  #[cfg(feature = "std")]
  #[inline]
  fn random_height() -> u32 {
    use rand::{thread_rng, Rng};
    let mut rng = thread_rng();
    let rnd: u32 = rng.gen();
    let mut h = 1;

    while h < MAX_HEIGHT && rnd <= PROBABILITIES[h] {
      h += 1;
    }
    h as u32
  }

  #[cfg(not(feature = "std"))]
  #[inline]
  fn random_height() -> u32 {
    use rand::{rngs::OsRng, Rng, RngCore};

    let rnd: u32 = OsRng.gen();
    let mut h = 1;

    while h < MAX_HEIGHT && rnd <= PROBABILITIES[h] {
      h += 1;
    }
    h as u32
  }

  fn insert_in(
    &self,
    key: &KeyRef<K>,
    value: &ValueRef<V>,
    ins: &mut Inserter<K, V>,
  ) -> Result<(), Error> {
    // Safety: a fresh new Inserter, so safe here
    if unsafe { self.find_splice(key, ins, false).0 } {
      return Err(Error::Duplicated);
    }

    #[cfg(all(test, feature = "std"))]
    if self.testing {
      // Add delay to make it easier to test race between this thread
      // and another thread that sees the intermediate state between
      // finding the splice and using it.
      std::thread::yield_now();
    }

    let (nd, height) = self.new_node(key, value)?;

    // We always insert from the base level and up. After you add a node in base
    // level, we cannot create a node in the level above because it would have
    // discovered the node in the base level.
    let mut invalid_date_splice = false;

    for i in 0..(height as usize) {
      let mut prev = ins.spl[i].prev;
      let mut next = ins.spl[i].next;

      if prev.is_null() {
        // New node increased the height of the skiplist, so assume that the
        // new level has not yet been populated.
        if !next.is_null() {
          panic!("next is expected to be nil, since prev is nil");
        }

        prev = self.head;
        next = self.tail;
      }

      // +----------------+     +------------+     +----------------+
      // |      prev      |     |     nd     |     |      next      |
      // | prevNextOffset |---->|            |     |                |
      // |                |<----| prevOffset |     |                |
      // |                |     | nextOffset |---->|                |
      // |                |     |            |<----| nextPrevOffset |
      // +----------------+     +------------+     +----------------+
      //
      // 1. Initialize prevOffset and nextOffset to point to prev and next.
      // 2. CAS prevNextOffset to repoint from next to nd.
      // 3. CAS nextPrevOffset to repoint from prev to nd.
      unsafe {
        loop {
          self
            .arena
            .write_tower(nd.offset as usize, i, prev.offset, next.offset);

          // Check whether next has an updated link to prev. If it does not,
          // that can mean one of two things:
          //   1. The thread that added the next node hasn't yet had a chance
          //      to add the prev link (but will shortly).
          //   2. Another thread has added a new node between prev and next.
          //
          // Safety: we already check next is not null
          let next_prev_offset = next.as_ptr().prev_offset(&self.arena, nd.offset, i);
          if next_prev_offset != prev.offset {
            // Determine whether #1 or #2 is true by checking whether prev
            // is still pointing to next. As long as the atomic operations
            // have at least acquire/release semantics (no need for
            // sequential consistency), this works, as it is equivalent to
            // the "publication safety" pattern.
            let prev_next_offset = prev.as_ptr().next_offset(&self.arena, prev.offset, i);
            if prev_next_offset == next.offset {
              // Ok, case #1 is true, so help the other thread along by
              // updating the next node's prev link.
              let link = self.arena.tower(next.offset as usize, i);
              let _ = link.prev_offset.compare_exchange(
                next_prev_offset,
                prev.offset,
                Ordering::AcqRel,
                Ordering::Acquire,
              );
            }
          }

          let prev_link = self.arena.tower(prev.offset as usize, i);

          match prev_link.next_offset.compare_exchange_weak(
            next.offset,
            nd.offset,
            Ordering::AcqRel,
            Ordering::Acquire,
          ) {
            Ok(_) => {
              // Managed to insert nd between prev and next, so update the next
              // node's prev link and go to the next level.
              #[cfg(all(test, feature = "std"))]
              if self.testing {
                // Add delay to make it easier to test race between this thread
                // and another thread that sees the intermediate state between
                // setting next and setting prev.
                std::thread::yield_now();
              }

              let next_link = self.arena.tower(next.offset as usize, i);
              let _ = next_link.prev_offset.compare_exchange(
                prev.offset,
                nd.offset,
                Ordering::AcqRel,
                Ordering::Acquire,
              );
              break;
            }
            Err(_) => {
              // CAS failed. We need to recompute prev and next. It is unlikely to
              // be helpful to try to use a different level as we redo the search,
              // because it is unlikely that lots of nodes are inserted between prev
              // and next.
              let fr = self.find_splice_for_level(key, i, prev);
              if fr.found {
                if i != 0 {
                  panic!("how can another thread have inserted a node at a non-base level?");
                }

                return Err(Error::Duplicated);
              }

              invalid_date_splice = true;
              prev = fr.splice.prev;
              next = fr.splice.next;
            }
          }
        }
      }
    }

    // If we had to recompute the splice for a level, invalidate the entire
    // cached splice.
    if invalid_date_splice {
      ins.height = 0;
    } else {
      // The splice was valid. We inserted a node between spl[i].prev and
      // spl[i].next. Optimistically update spl[i].prev for use in a subsequent
      // call to add.
      for i in 0..(height as usize) {
        ins.spl[i].prev = nd;
      }
    }
    Ok(())
  }

  #[allow(clippy::type_complexity)]
  fn new_node(
    &self,
    key: &KeyRef<K>,
    value: &ValueRef<V>,
  ) -> Result<(NodePtr<K::Trailer, V::Trailer>, u32), Error> {
    let height = Self::random_height();
    let nd = Node::new_node_ptr(&self.arena, height, key, value)?;

    // Try to increase self.height via CAS.
    let mut list_height = self.height();
    while height > list_height {
      match self.height.compare_exchange_weak(
        list_height,
        height,
        Ordering::SeqCst,
        Ordering::Acquire,
      ) {
        // Successfully increased skiplist.height.
        Ok(_) => break,
        Err(h) => list_height = h,
      }
    }
    Ok((nd, height))
  }

  // findNear finds the node near to key.
  // If less=true, it finds rightmost node such that node.key < key (if allowEqual=false) or
  // node.key <= key (if allowEqual=true).
  // If less=false, it finds leftmost node such that node.key > key (if allowEqual=false) or
  // node.key >= key (if allowEqual=true).
  // Returns the node found. The bool returned is true if the node has key equal to given key.
  unsafe fn find_near(
    &self,
    key: &KeyRef<K>,
    less: bool,
    allow_equal: bool,
  ) -> (NodePtr<K::Trailer, V::Trailer>, bool) {
    let mut curr = self.head;
    let mut level = (self.height() - 1) as usize;
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
          return (NodePtr::NULL, false);
        }

        // Try to return curr. Make sure it is not a curr node.
        if curr.offset == self.head.offset {
          return (NodePtr::NULL, false);
        }
        return (curr, false);
      }

      // Safety: we have checked next is not null
      let next_key = next.as_ptr().get_key(&self.arena);
      match self.cmp.compare(key.as_bytes(), next_key) {
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
          if curr.offset == self.head.offset {
            return (NodePtr::NULL, false);
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
            let rt = self.get_next(next, 0);
            return (rt, false);
          }

          // We want <. If not base level, we should go closer in the next level.
          if level > 0 {
            level -= 1;
            continue;
          }

          // On base level. Return curr.
          if curr.offset == self.head.offset {
            return (NodePtr::NULL, false);
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

  /// ## Safety:
  /// - All of splices in the inserter must be contains node ptrs are allocated by the current skip map.
  unsafe fn find_splice(
    &self,
    key: &KeyRef<K>,
    ins: &mut Inserter<K, V>,
    returned_when_found: bool,
  ) -> (bool, Option<NodePtr<K::Trailer, V::Trailer>>) {
    let list_height = self.height();
    let mut level = 0;

    let mut prev = self.head;
    if ins.height < list_height {
      // Our cached height is less than the list height, which means there were
      // inserts that increased the height of the list. Recompute the splice from
      // scratch.
      ins.height = list_height;
      level = ins.height as usize;
    } else {
      // Our cached height is equal to the list height.
      while level < list_height as usize {
        let spl = &ins.spl[level];
        if self.get_next(spl.prev, level).offset != spl.next.offset {
          level += 1;
          // One or more nodes have been inserted between the splice at this
          // level.
          continue;
        }

        if spl.prev.offset != self.head.offset && !self.key_is_after_node(spl.prev, key) {
          // Key lies before splice.
          level = list_height as usize;
          break;
        }

        if spl.next.offset != self.tail.offset && !self.key_is_after_node(spl.next, key) {
          // Key lies after splice.
          level = list_height as usize;
          break;
        }

        // The splice brackets the key!
        prev = spl.prev;
        break;
      }
    }

    let mut lvl = level;
    let mut found = false;
    while lvl > 0 {
      let mut fr = self.find_splice_for_level(key, level - 1, prev);
      if fr.splice.next.ptr.is_null() {
        fr.splice.next = self.tail;
      }
      found = fr.found;
      if found && returned_when_found {
        return (found, fr.curr);
      }
      ins.spl[lvl] = fr.splice;
      lvl -= 1;
    }

    (found, None)
  }

  /// ## Safety
  /// - `level` is less than `MAX_HEIGHT`.
  /// - `start` must be allocated by self's arena.
  unsafe fn find_splice_for_level(
    &self,
    key: &KeyRef<K>,
    level: usize,
    start: NodePtr<K::Trailer, V::Trailer>,
  ) -> FindResult<K, V> {
    let mut prev = start;

    loop {
      // Assume prev.key < key.
      let next = self.get_next(prev, level);
      if next.offset == self.tail.offset {
        // Tail node, so done.
        return FindResult {
          splice: Splice { prev, next },
          found: false,
          curr: None,
        };
      }

      // offset is not zero, so we can safely dereference the next node ptr.
      let next_node = &*next.ptr;

      let (key_offset, key_size) = (next_node.key_offset, next_node.key_size);
      let next_key = self.arena.get_bytes(key_offset as usize, key_size as usize);

      match self.cmp.compare(key.as_bytes(), next_key) {
        // We are done for this level, since prev.key < key < next.key.
        cmp::Ordering::Less => {
          return FindResult {
            splice: Splice { prev, next },
            found: false,
            curr: None,
          };
        }
        // Keep moving right on this level.
        cmp::Ordering::Greater => prev = next,
        cmp::Ordering::Equal => {
          // User-key equality.
          let trailer = key.trailer();

          if next_node.key_trailer.eq(trailer) {
            // Internal key equality.
            return FindResult {
              splice: Splice { prev, next },
              found: true,
              curr: Some(next),
            };
          }

          if trailer.gt(&next_node.key_trailer) {
            // We are done for this level, since prev.key < key < next.key.
            return FindResult {
              splice: Splice { prev, next },
              found: false,
              curr: None,
            };
          }
        }
      }
    }
  }

  /// ## Safety
  /// - The caller must ensure that the node is allocated by the arena.
  /// - The caller must ensure that the node is not null.
  unsafe fn key_is_after_node(&self, nd: NodePtr<K::Trailer, V::Trailer>, key: &KeyRef<K>) -> bool {
    let nd = &*nd.ptr;
    let nd_key = self
      .arena
      .get_bytes(nd.key_offset as usize, nd.key_size as usize);

    match self.cmp.compare(nd_key, key.as_bytes()) {
      cmp::Ordering::Less => true,
      cmp::Ordering::Greater => false,
      cmp::Ordering::Equal => {
        // User-key equality.
        let key_trailer = key.trailer();
        if nd.key_trailer.eq(key_trailer) {
          // Trailer equality.
          return false;
        }
        nd.key_trailer.le(key_trailer)
      }
    }
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[inline]
  unsafe fn get_prev(
    &self,
    nd: *const Node<K::Trailer, V::Trailer>,
    offset: u32,
    height: usize,
  ) -> NodePtr<K, V> {
    match nd.as_ref() {
      None => NodePtr::NULL,
      Some(nd) => {
        let offset = nd.prev_offset(&self.arena, offset, height);
        let ptr = self.arena.get_pointer(offset as usize);
        NodePtr::new(ptr, offset)
      }
    }
  }

  /// ## Safety
  ///
  /// - The caller must ensure that the node is allocated by the arena.
  #[inline]
  unsafe fn get_next(
    &self,
    nptr: NodePtr<K::Trailer, V::Trailer>,
    height: usize,
  ) -> NodePtr<K::Trailer, V::Trailer> {
    match nptr.ptr.as_ref() {
      None => NodePtr::NULL,
      Some(nd) => {
        let offset = nd.next_offset(&self.arena, nptr.offset, height);
        let ptr = self.arena.get_pointer(offset as usize);
        NodePtr::new(ptr, offset)
      }
    }
  }
}

pub struct Inserter<'a, K: Key, V: Value> {
  spl: [Splice<K, V>; MAX_HEIGHT],
  height: u32,
  _m: core::marker::PhantomData<&'a ()>,
}

impl<'a, K: Key, V: Value> Default for Inserter<'a, K, V> {
  #[inline]
  fn default() -> Self {
    Self {
      spl: [Splice::default(); MAX_HEIGHT],
      height: 0,
      _m: core::marker::PhantomData,
    }
  }
}

struct Splice<K: Key, V: Value> {
  prev: NodePtr<K::Trailer, V::Trailer>,
  next: NodePtr<K::Trailer, V::Trailer>,
}

impl<K: Key, V: Value> Default for Splice<K, V> {
  #[inline]
  fn default() -> Self {
    Self {
      prev: NodePtr::NULL,
      next: NodePtr::NULL,
    }
  }
}

impl<K: Key, V: Value> Clone for Splice<K, V> {
  #[inline]
  fn clone(&self) -> Self {
    *self
  }
}

impl<K: Key, V: Value> Copy for Splice<K, V> {}

struct FindResult<K: Key, V: Value> {
  found: bool,
  splice: Splice<K, V>,
  curr: Option<NodePtr<K::Trailer, V::Trailer>>,
}
