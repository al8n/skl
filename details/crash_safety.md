# Crash-safety in on-disk mode

Durability is a fundamental attribute of storage systems, ensuring that data remains intact and consistent even in the event of a program crash or power failure. It guarantees that when the system is restarted, the storage will continue to function correctly, without encountering any undefined behaviors or data corruption.

In a lock-free skiplist implementation like SkipMap, which is based on an ARENA allocator backed by a memory-mapped file, guaranteeing crash or power failure safety can be challenging. This is because changes are initially written to dirty pages in memory. If a crash or power failure occurs, the system may not be able to ensure that these changes are fully persisted to disk, leading to potential data loss or corruption. However, is it truly impossible to achieve such guarantees?

Before we start, let keeps the some important things in mind:

1. The node structure

    ```rust
    #[derive(Debug)]
    #[repr(C)]
    struct Link {
      next_offset: AtomicU32,
      prev_offset: AtomicU32,
    }

    // node size is 24 bytes in total
    #[repr(C)]
    struct Node<T> {
      /// Multiple parts of the value are encoded as a single u64 so that it
      /// can be atomically loaded and stored:
      ///   value offset: u32 (bits 0-31)
      ///   value size  : u32 (bits 32-63)
      value: AtomicU64,
      // Immutable. No need to lock to access key.
      key_offset: u32,
      // Immutable. No need to lock to access key.
      key_size_and_height: u32,
      // The state of the node, 0 means initialized but not committed, 1 means committed.      
      state: AtomicU8,

      // u56 (7 bytes) for storing version (MVCC purpose)
      version1: u8,
      version2: u8,
      version3: u8,
      version4: u8,
      version5: u8,
      version6: u8,
      version7: u8,

      trailer: PhantomData<T>,

      // ** DO NOT REMOVE BELOW COMMENT**
      // The below field will be attached after the node, have to comment out
      // this field, because each node will not use the full height, the code will
      // not allocate the full size of the tower.
      //
      // Most nodes do not need to use the full height of the tower, since the
      // probability of each successive level decreases exponentially. Because
      // these elements are never accessed, they do not need to be allocated.
      // Therefore, when a node is allocated in the arena, its memory footprint
      // is deliberately truncated to not include unneeded tower elements.
      //
      // All accesses to elements should use CAS operations, with no need to lock.
      // pub(super) tower: [Link; self.opts.max_height],
    }
    ```

2. An entry of skiplist is aligned in ARENA like this

    ```text
    |              Full node              |    |  key part |    |               value part             |          
    | Node | some links (1 to max height) | .. |   key     | .. | some padding bytes | trailer | value |
    ```

   1. The full node part will be frequently updated
   2. key part and value part will never be updated
   3. `..` means that there may or may not some bytes

Now, let's review how a new entry is created and inserted to the skiplist in memory mode.

1. Initialized phase
   `insert(key, value)`
   1. Acquire enough continuous space from the underlying ARENA.
   2. Construct a node from buffer, and then copy key and value to the buffer.

2. Insertion phase

    ```text
    +------------------+     +-------------+     +------------------+
    |      prev        |     |   new_node  |     |        next      |
    | prev_next_offset |---->|             |     |                  |
    |                  |<----| prev_offset |     |                  |
    |                  |     | next_offset |---->|                  |
    |                  |     |             |<----| next_prev_offset |
    +------------------+     +-------------+     +------------------+
    ```

   1. Initialize the `new_node`'s `prev_offset` and `next_offset` to point to prev node and next node.
   2. CAS `prev_next_offset` to repoint from next node to new node.
   3. CAS `next_prev_offset` to repoint from prev to new node.

Now, let's analyze crash happens on different stage one by one.

- 1.1
  - If a crash happens after 1.1, then everything is good, we do not modify the skiplist at the moment
- 1.2
  - If a crash happens during 1.2, then it is also good, we still do not update the skiplist, the underlying allocator may be partially or fully persisted on disk, but it is ok, because no pointers in skiplist point to such chunk.
- 2.1
  - If a crash happens during 2.1, then it is also good, we still do not update the skiplist, the underlying allocator may be partially or fully persisted on disk, but it is ok, because no pointers in skiplist point to such chunk.
- 2.2
  - If a crash happens during 2.2, it is good, because it means that the update on the skiplist's node fails. However, this operation happens on an `AtomicU32`, there is no intermediate state, so the skiplist still has no changes!
  - If a crash happens after 2.2, which means that the prev's `next_offset` is successfully updated in memory, it points to the buffer holds the new node, but the changes on the buffer of previous node and the buffer of the new node may split into multiple pages, and those pages may or may not be persisted.

    Yes, we have problem now! Let's analyze the problems and possible situations:

    Let's assume the page size is 4KB, the underyling memory mapped file size is 2GB.

    1. It is possible that the `AtomicU32` (4 bytes) split into two pages, e.g. the first two bytes at offset 4095 and 4096 in page1, the last two bytes at 4097 and 4098 in page2. In this situation, it is possible page1 is flushed by system, but page2 does not. How to solve it?

      Answer: when acquiring memory buffer for above `Node` structure, we can make sure the `Node` + `Link`s (without key part and value part) in the same page, in this way, there is only two situations when crash:

      1. if the page is persisted, then the update on the `Node` and its `tower` are also persisted,
      2. if the page is not persisted, then the `Node` and its `tower` keep old value, when restarting, we still in a valid status.

    2. changes on the buffer of previous node are a
    But we can solve it by manually flush the changes on such buffer (`msync(buffer_offset, buffer_size)`) to disk after 2.1 success.

    So, when the crash happens