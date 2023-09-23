use core::cmp;

use crate::{KeyRef, ValueRef, key::AsKeyRef};

use super::{Key, Value, SkipMap, Comparator, node::NodePtr, FindResult};


/// An iterator over the skipmap. The current state of the iterator can be cloned by
/// simply value copying the struct.
pub struct Iterator<'a, K: Key, V: Value, C: Comparator = ()> {
  map: &'a SkipMap<K, V, C>,
  nd: NodePtr<K::Trailer, V::Trailer>,
  lower: &'a [u8],
  upper: &'a [u8],
}

impl<'a, K: Key, V: Value, C: Comparator> Iterator<'a, K, V, C> {
  /// Creates a new iterator over the skipmap.
  pub fn new(map: &'a SkipMap<K, V, C>) -> Self {
    // Self {
    //   map,
    //   nd: map.head(),
    //   lower: &[],
    //   upper: &[],
    // }
    todo!()
  }

  /// Creates a new iterator over the skipmap with the given lower and upper bounds.
  pub fn new_bound(map: &'a SkipMap<K, V, C>, lower: &'a [u8], upper: &'a [u8]) -> Self {
    // Self {
    //   map,
    //   nd: map.head(),
    //   lower,
    //   upper,
    // }
    todo!()
  }

  /// Returns the key of the current entry.
  pub fn key(&self) -> Option<KeyRef<'_, K>> {
    if self.nd.is_null() {
      return None;
    }

    // Safety:
    // 1. the nd is valid, we already check this on line 42
    // 2. the node is allocated by the map's arena, so the key is valid
    unsafe {
      Some(self.key_unchecked())
    }
  }

  /// Returns the key of the current entry without any checks.
  /// 
  /// ## Safety
  /// - The current node must be valid
  pub unsafe fn key_unchecked(&self) -> KeyRef<'_, K> {
    let nd = self.nd.as_ptr();
    let val = nd.get_key(&self.map.arena);
    KeyRef::new(val, &nd.key_trailer)
  } 

  /// Returns the value of the current entry.
  pub fn value(&self) -> Option<ValueRef<'_, V>> {
    if self.nd.is_null() {
      return None;
    }

    // Safety:
    // 1. the nd is valid, we already check this on line 58
    // 2. the node is allocated by the map's arena, so the value is valid
    unsafe {
      let nd = self.nd.as_ptr();
      let val = nd.get_value(&self.map.arena);
      Some(ValueRef::new(val, nd.value_trailer))
    }
  }

  /// Returns the value of the current entry without any checks.
  ///
  /// ## Safety
  /// - The current node must be valid
  pub unsafe fn value_unchecked(&self) -> ValueRef<'_, V> {
    let nd = self.nd.as_ptr();
    let val = nd.get_value(&self.map.arena);
    ValueRef::new(val, nd.value_trailer)
  }

  /// Returns the key of the current entry.
  pub fn key_owned(self) -> K {
    // self.nd.key_owned()
    todo!()
  }

  /// Returns the value of the current entry.
  pub fn value_owned(self) -> V {
    // self.nd.value_owned()
    todo!()
  }

  /// Seeks position at the first entry in map. Returns the key and value
  /// if the iterator is pointing at a valid entry, and `None` otherwise. Note
  /// that First only checks the upper bound. It is up to the caller to ensure
  /// that key is greater than or equal to the lower bound (e.g. via a call to `seek_ge(lower)`).
  pub fn first<'b: 'a>(&'a mut self) -> Option<(KeyRef<'a, K>, ValueRef<'a, V>)>
  where
    K::Trailer: 'b,
    V::Trailer: 'b, 
  {
    unsafe {
      self.nd = self.map.get_next(self.map.head, 0);
      if self.nd.ptr == self.map.tail.ptr {
        return None;
      }

      if !self.upper.is_empty() {
        // Safety: the nd is valid, we already check this on line 113
        let node = self.nd.as_ptr();
        // Safety: the node is allocated by the map's arena, so the key is valid
        if let cmp::Ordering::Less | cmp::Ordering::Equal = self.map.cmp.compare(self.upper, node.get_key(&self.map.arena)) {
          self.nd = self.map.tail;
          return None;
        }
      }

      Some((self.key_unchecked(), self.value_unchecked()))
    }
  }

  /// Seeks position at the last entry in list. Returns the key and value if
  /// the iterator is pointing at a valid entry, and `None` otherwise. Note
  /// that Last only checks the lower bound. It is up to the caller to ensure that
  /// key is less than the upper bound (e.g. via a call to `seek_lt(upper)`).
  pub fn last<'b: 'a>(&'a mut self) -> Option<(KeyRef<'a, K>, ValueRef<'a, V>)>
  where
    K::Trailer: 'b,
    V::Trailer: 'b, 
  {
    unsafe {
      self.nd = self.map.get_prev(self.map.tail, 0);
      if self.nd.ptr == self.map.head.ptr {
        return None;
      }

      if !self.lower.is_empty() {
        // Safety: the nd is valid, we already check this on line 142
        let node = self.nd.as_ptr();
        // Safety: the node is allocated by the map's arena, so the key is valid
        if let cmp::Ordering::Greater = self.map.cmp.compare(self.lower, node.get_key(&self.map.arena)) {
          self.nd = self.map.head;
          return None;
        }
      }
      Some((self.key_unchecked(), self.value_unchecked()))
    }
  }

  

  /// Moves the iterator to the first entry whose key is greater than or
  /// equal to the given key. Returns the key and value if the iterator is
  /// pointing at a valid entry, and (nil, nil) otherwise. Note that `seek_ge` only
  /// checks the upper bound. It is up to the caller to ensure that key is greater
  /// than or equal to the lower bound.
  pub fn seek_ge<'b: 'a, Q>(&'a mut self, key: &'b Q) -> Option<(KeyRef<'a, K>, ValueRef<'a, V>)>
  where
    K::Trailer: 'b,
    V::Trailer: 'b,
    Q: Ord + ?Sized + AsKeyRef<Key = K>,
  {
    let res = self.seek_for_base_splice(key.as_key_ref());
    self.nd = res.next;
    if self.nd.ptr == self.map.tail.ptr {
      return None;
    }

    if !self.upper.is_empty() {
      unsafe {
        // Safety: the nd is valid, we already check this on line 75
        let node = self.nd.as_ptr();
        // Safety: the node is allocated by the map's arena, so the key is valid
        if let cmp::Ordering::Less | cmp::Ordering::Equal = self.map.cmp.compare(self.upper, node.get_key(&self.map.arena)) {
          self.nd = self.map.tail;
          return None;
        }
      }
    }

    // Safety: the nd is valid, we already check this on line 115
    unsafe {
      Some((self.key_unchecked(), self.value_unchecked()))
    }
  }

  /// Moves the iterator to the last entry whose key is less than the given
  /// key. Returns the key and value if the iterator is pointing at a valid entry,
  /// and `None` otherwise. Note that `seek_lt` only checks the lower bound. It
  /// is up to the caller to ensure that key is less than the upper bound.
  pub fn seek_lt<'b: 'a, Q>(&'a mut self, key: &'b Q) -> Option<(KeyRef<'a, K>, ValueRef<'a, V>)>
  where
    K::Trailer: 'b,
    V::Trailer: 'b,
    Q: Ord + ?Sized + AsKeyRef<Key = K>,
  {
    // NB: the top-level Iterator has already adjusted key based on
	  // the upper-bound.
    let res = self.seek_for_base_splice(key.as_key_ref());
    self.nd = res.prev;
    if self.nd.ptr == self.map.head.ptr {
      return None;
    }

    if !self.lower.is_empty() {
      unsafe {
        // Safety: the nd is valid, we already check this on line 75
        let node = self.nd.as_ptr();
        // Safety: the node is allocated by the map's arena, so the key is valid
        if let cmp::Ordering::Greater = self.map.cmp.compare(self.lower, node.get_key(&self.map.arena)) {
          self.nd = self.map.head;
          return None;
        }
      }
    }

    // Safety: the nd is valid, we already check this on line 115
    unsafe {
      Some((self.key_unchecked(), self.value_unchecked()))
    }
  }
}

impl<'a, K: Key, V: Value, C: Comparator> Iterator<'a, K, V, C> {
  fn seek_for_base_splice(&self, key: KeyRef<K>) -> SeekResult<K, V> {
    let mut lvl = (self.map.height() - 1) as usize;

    let mut prev = self.map.head;
    let mut next = NodePtr::NULL;
    let mut found = false;

    loop {
      let fr = unsafe { self.map.find_splice_for_level(&key, lvl, prev) };
      prev = fr.splice.prev;
      next = fr.splice.next;
      found = fr.found;
      if found {
        if lvl != 0 {
          // next is pointing at the target node, but we need to find previous on
				  // the bottom level.

          // Safety: the next we use here is got from the find_splice_for_level, so must be allocated by the same arena
          prev = unsafe { self.map.get_prev(next, 0) };
        }
        break;
      }

      if lvl == 0 {
        break;
      }

      lvl -= 1;
    }

    SeekResult { prev, next, found }
  }
}

struct SeekResult<K: Key, V: Value> {
  prev: NodePtr<K::Trailer, V::Trailer>,
  next: NodePtr<K::Trailer, V::Trailer>,
  found: bool,
}