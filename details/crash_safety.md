# Crash-Safety in On-Disk Mode

Durability is a fundamental attribute of storage systems, ensuring that data remains intact and consistent even in the event of a program crash or power failure. It guarantees that when the system is restarted, the storage system will continue to function correctly, without encountering undefined behaviors or data corruption.

In a lock-free skiplist implementation like SkipMap, which is based on an ARENA allocator backed by a memory-mapped file, ensuring crash or power failure safety can be particularly challenging. This is because changes are initially written to dirty pages in memory. If a crash or power failure occurs, the system may not be able to guarantee that these changes are fully persisted to disk, potentially leading to data loss or corruption. However, is it truly impossible to achieve such guarantees?

Before diving deeper, let's keep some important considerations in mind:

1. The Node Structure

   ```rust
    #[derive(Debug)]
    #[repr(C)]
    struct Link {
      next_offset: AtomicU32,
      prev_offset: AtomicU32,
    }

    // Node size is 24 bytes in total (excluding `tower`)
    #[repr(C)]
    struct Node<T> {
      // Multiple parts of the value are encoded as a single u64 so that it
      // can be atomically loaded and stored:
      //   value offset: u32 (bits 0-31)
      //   value size  : u32 (bits 32-63)
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

2. Skiplist Entry Alignment in ARENA
    A skiplist entry is aligned in the ARENA as follows:

    ```text
    |              Full node              |    |  key part |    |               value part             |          
    | Node | some links (1 to max height) | .. |   key     | .. | some padding bytes | trailer | value |
    ```

    1. The full node part will be frequently updated.
    2. The key part and value part will never be updated.
    3. `..` indicates that there may or may not be some bytes.
3. Atomic Operations and Partial Writes

   The `Atomic*` types in Rust, such as `AtomicU64`, provide atomicity guarantees for operations. This means that updates to an `AtomicU64`, which spans 8 bytes in memory, are indivisible. The operation ensures that all 8 bytes are either fully updated in a single, uninterrupted step, or not updated at all. This prevents partial writes, thereby ensuring consistency and preventing race conditions in multi-threaded environments.

4. Dirty Pages and Synchronization in Memory-Mapped Files

    When working with memory-mapped files, any modification to the mapped region marks the corresponding memory pages as dirty, indicating that they have been changed but not yet written to disk. The operating system periodically flushes these dirty pages to the underlying storage, ensuring data persistence. You can also manually trigger this process using the msync function.

    Importantly, the system ensures that when a page is flushed, it is either fully written to disk or not written at all. This atomicity at the page level prevents partial writes, ensuring that the integrity of data on disk is maintained even in the event of a system crash or power failure.

## Node insertion in full memory mode

Let's review how a new entry is created and inserted into the skiplist in memory mode.

1. Initialization Phase

   1. Acquire enough continuous space from the underlying ARENA.
   2. Construct a node from the buffer, then copy the key and value to the buffer.

2. Insertion Phase

    ```text
    +------------------+     +-------------+     +------------------+
    |      prev        |     |   new_node  |     |        next      |
    | prev_next_offset |---->|             |     |                  |
    |                  |<----| prev_offset |     |                  |
    |                  |     | next_offset |---->|                  |
    |                  |     |             |<----| next_prev_offset |
    +------------------+     +-------------+     +------------------+
    ```

   1. Initialize the new_node's `prev_offset` and `next_offset` to point to the previous node and the next node.
   2. CAS `prev_next_offset` to repoint from the next node to the new node.
   3. CAS `next_prev_offset` to repoint from the previous node to the new node.

## Crash Analysis at Each Stage

Let's analyze what happens if a crash occurs at different stages:

### 1.1 Crash During Memory Allocation

**Scenario:** If a crash happens after memory allocation (step 1.1), there’s no impact on the skiplist because no modifications have been made yet. The allocator may have partially or fully persisted the allocated memory on disk, but since no pointers in the skiplist point to this chunk, it's safe.

### 1.2 Crash During Node Construction

**Scenario:** If a crash occurs during node construction (step 1.2), the situation is still safe. The skiplist remains unmodified, and while the underlying allocator may have partially or fully persisted data to disk, no skiplist pointers reference this data.

### 2.1 Crash During Node Initialization

**Scenario:** If a crash happens during node initialization (step 2.1), the skiplist is still unmodified. The underlying allocator might have persisted some data, but since the skiplist pointers haven't been updated, there’s no risk.

### 2.2 Crash During `prev_next_offset` Update

**Scenario 1:** If a crash happens during the update of prev_next_offset (step 2.2), it’s safe because the update on the skiplist node hasn’t completed. Since this operation involves an AtomicU32, there is no intermediate state, so the skiplist remains unchanged.

**Scenario 2:** If a crash occurs after successfully updating prev_next_offset but before flushing the corresponding pages, this can lead to issues. The previous node might now point to the new node, but if the pages containing the new node are not persisted, the skiplist could be left in an inconsistent state.

**Problem:** If the page containing the previous node’s pointer is persisted but the page containing the new node is not, the previous node will point to an invalid or zeroed-out buffer, leading to undefined behavior.

**Solution:**

Ensure that the `Node` and its associated `Link`s (without the key and value parts) reside within the same page. This way, the entire node is either fully persisted or not, preventing partial updates.Manually flush the page containing the new node after initializing it to ensure that it’s persisted before updating the previous node’s pointer.

### 2.3 Crash During `next_prev_offset` Update

**Scenario:** This step can lead to multiple scenarios, but the most complex involves the previous node in page1, the new node in page2, and the next node in page3. After the new node is constructed and flushed, the possible outcomes are:

1. **page1 Flushed, page3 Changes Lost:** The previous node points to the new node, but the new node's `next_offset` is incorrect, leading to inconsistencies.
2. **page1 Changes Lost, page3 Flushed:** The previous node's pointer remains unchanged, but the new node is linked to the next node, creating a disjointed list.
3. **page1 and page3 Changes Lost:** The new node is not linked to the skiplist, which is safe as the skiplist remains in its old valid state.

**Solution:**

Use a two-phase commit approach. Initially, mark the new node as "initialized but not committed." This way, during iteration, insertion, and searching, the node is ignored until it is fully committed.
After all necessary pages are flushed, mark the new node as committed. If a crash happens before this final step, the skiplist remains in its old valid state. If the commit is flushed, the skiplist transitions to the new valid state.

## Conclusion

In this lock-free skiplist implementation in Rust, based on an ARENA allocator backed by a memory-mapped file, we can achieve crash safety by:

1. Ensuring atomicity in memory allocation and pointer updates.
2. Carefully controlling the flushing of pages to disk, particularly after critical updates.
3. Using a two-phase commit approach to handle partial updates and maintain consistency in the face of crashes or power failures.

By following these strategies, we can ensure that the skiplist remains consistent and durable, even under adverse conditions.
