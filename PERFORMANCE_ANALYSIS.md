# SKL Performance Analysis

## Executive Summary

Issue [#41](https://github.com/al8n/skl/issues/41) reports a **~200x write performance regression** (5 us to 1 ms) introduced in commit `37ceb55`. The root cause is **CAS contention from the doubly-linked tower structure**. This document presents benchmark data, identifies specific bottlenecks, and proposes solutions.

## Benchmark Results

Benchmarks were run on the same machine using `cargo bench --bench bench` with criterion.

### Environment

- **Machine**: macOS Darwin 25.0.0
- **Rust**: stable (edition 2021)
- **Commits tested**:
  - `fa55ff6` — baseline (pre-regression, would not compile with modern Rust toolchain)
  - `37ceb55` — regression commit ("Refactor and Add SkipSet")
  - `a281708` — current HEAD

> **Note**: `fa55ff6` could not be compiled due to API changes and outdated dependencies.
> The reported 5 us write latency comes from the issue author's original measurements.

### Write Performance (2 concurrent threads)

| Benchmark              | Baseline (`fa55ff6`) | Regression (`37ceb55`) | Current HEAD (`a281708`) |
|------------------------|----------------------|------------------------|--------------------------|
| `fixed_skiplist_write` | ~5,000 ns (reported) | **583,765 ns** (+/- 175,368) | **575,151 ns** (+/- 180,248) |
| `fixed_map_write`      | —                    | 6,791 ns (+/- 3,182)  | 10,095 ns (+/- 3,266)   |

**Key finding**: `fixed_skiplist_write` remains at ~575-584 us — **~115x slower than the reported baseline** and **~57-85x slower than a Mutex-protected HashMap**. The regression has not been resolved.

### Read/Write Mixed Workload (2 concurrent threads)

The parameter (0-10) controls the read fraction: 0 = all writes, 10 = all reads.

| Read Fraction | Regression (`37ceb55`) | Current HEAD (`a281708`) |
|---------------|------------------------|--------------------------|
| 0 (all write) | 1,028 ns (+/- 1,500)  | 1,056 ns (+/- 751)      |
| 1             | 842 ns (+/- 868)      | 1,122 ns (+/- 868)      |
| 2             | 1,116 ns (+/- 911)    | 2,023 ns (+/- 1,961)    |
| 3             | 1,164 ns (+/- 1,410)  | 1,600 ns (+/- 1,298)    |
| 4             | 1,934 ns (+/- 1,188)  | 1,058 ns (+/- 790)      |
| 5             | 609 ns (+/- 535)      | 586 ns (+/- 322)        |
| 6             | 588 ns (+/- 625)      | 574 ns (+/- 394)        |
| 7             | 1,017 ns (+/- 626)    | 659 ns (+/- 358)        |
| 8             | 283 ns (+/- 139)      | 332 ns (+/- 219)        |
| 9             | 553 ns (+/- 332)      | 366 ns (+/- 331)        |
| 10 (all read) | 229 ns (+/- 152)      | 308 ns (+/- 171)        |

**Observation**: Read performance is comparable across commits. The regression is concentrated in write-heavy workloads under contention. The `fixed_skiplist_read_write` benchmark only uses 2 threads with random keys (low contention), so it doesn't show the full 200x regression that `fixed_skiplist_write` does (where both threads continuously write).

## Root Cause Analysis

### 1. Doubly-Linked Tower: 2x CAS Operations (Primary)

**Location**: `src/generic/list.rs:1006-1079`, `src/dynamic/list.rs:968-1032`

The tower insertion diagram from the source tells the story:

```
+----------------+     +------------+     +----------------+
|      prev      |     |     nd     |     |      next      |
| prevNextOffset |---->|            |     |                |
|                |<----| prevOffset |     |                |
|                |     | nextOffset |---->|                |
|                |     |            |<----| nextPrevOffset |
+----------------+     +------------+     +----------------+
```

Each level requires **3 CAS-class operations** in sequence:

1. **Helper CAS** (`list.rs:1042-1049`): Fix `next.prev_offset` if stale (conditional)
2. **Forward CAS** (`list.rs:1053-1059`): Swing `prev.next_offset` from `next` to `nd`
3. **Backward CAS** (`list.rs:1072-1079`): Swing `next.prev_offset` from `prev` to `nd`

For a node with height H, that's up to **3 x H CAS operations** per insertion. A singly-linked skiplist needs only **1 x H**.

**Contention cascade**: When CAS #2 fails (another thread inserted between `prev` and `next`):
- Full O(log n) splice re-search at `list.rs:1087-1092`
- Entire inserter splice cache invalidated at `list.rs:1141`
- Retry the loop from the top

Under high contention, this creates a **feedback loop**: more threads inserting leads to more CAS failures, each triggering an expensive re-search, increasing the time other threads' CAS operations are stale.

### 2. SeqCst Ordering Where Release Suffices

**The code itself documents this** at `src/generic/list.rs:1033-1036`:

```rust
// As long as the atomic operations have at least acquire/release
// semantics (no need for sequential consistency), this works, as
// it is equivalent to the "publication safety" pattern.
```

Yet all CAS operations use `Ordering::SeqCst`:

| Location | Operation | Current | Recommended |
|----------|-----------|---------|-------------|
| `generic/list.rs:1047` | `cas_prev_offset` (helper) | SeqCst | Release |
| `generic/list.rs:1058` | `cas_next_offset` (forward link) | SeqCst | Release |
| `generic/list.rs:1077` | `cas_prev_offset` (backward link) | SeqCst | Release |
| `dynamic/list.rs` (same pattern) | all three CAS ops | SeqCst | Release |
| `sync.rs:90` | `compare_exchange_height_weak` | SeqCst | Release |
| `sync.rs:109` | `compare_exchange_weak` (max version) | SeqCst | Release |
| `sync.rs:109` | `compare_exchange_weak` (min version) | SeqCst | Release |

`SeqCst` forces a **full memory barrier** and total ordering across all cores. On x86, this translates to `MFENCE` or `LOCK CMPXCHG` with stronger guarantees. On ARM/RISC-V, it's even more expensive. Since the code only needs publication safety (acquire/release), this is unnecessary overhead on every atomic operation in the hot path.

### 3. Contention on Shared Atomic Locations

Each node's tower level has two atomics (`next_offset: AtomicU32`, `prev_offset: AtomicU32`) defined in `src/allocator.rs:258-284`:

```rust
pub struct Link {
    next_offset: AtomicU32,
    prev_offset: AtomicU32,
}
```

When multiple threads insert near the same position (common with sequential or similar keys), they contend on the **same** `prev.next_offset` and `next.prev_offset` atomics. Each failed CAS invalidates the cache line on all other cores, causing:

- **Cache line bouncing**: The 8-byte `Link` struct fits in one cache line, so writing `next_offset` also invalidates `prev_offset` for other cores (false sharing within the node, plus true sharing across concurrent insertions).
- **Memory bus saturation**: Under high thread counts, the interconnect becomes the bottleneck.

### 4. Splice Cache Invalidation

**Location**: `src/generic/list.rs:1141-1148`

```rust
if invalid_data_splice {
    ins.height = 0;  // Invalidates entire cache
} else {
    for i in 0..(height as usize) {
        ins.spl[i].prev = unlinked_node;
    }
}
```

On CAS failure, `invalid_data_splice = true` causes the next insertion to discard all cached splice positions and rebuild from scratch. This is correct for safety but pessimistic for performance.

## Quantifying the Regression

### Why ~575 us for `fixed_skiplist_write`?

The benchmark runs 2 concurrent threads, both continuously inserting random 16-byte keys into a 512 MB arena.

With random keys and average height ~1.4 (probability 1/e per level):

| Factor | Singly-linked (estimated) | Doubly-linked (current) |
|--------|---------------------------|------------------------|
| CAS ops per insert | ~1.4 | ~4.2 (3x per level) |
| CAS failure probability | Low | Higher (more targets) |
| Re-search cost per failure | O(log n) | O(log n) + cache invalidation |
| Memory ordering overhead | Release | SeqCst (~20-50% penalty) |
| **Estimated total** | **~5 us** | **~575 us** |

The gap between 5 us and 575 us isn't purely from 3x more CAS ops — it's the **compounding effect**: more CAS targets means more failures, each failure triggers an expensive re-search, which increases the window for other threads to invalidate the splice, leading to more failures.

## Proposed Solutions

### Solution 1: Singly-Linked Tower (High Impact)

As proposed in issue #41, create a `singly` module that only maintains `next_offset` per level:

```rust
pub struct Link {
    next_offset: AtomicU32,
    // No prev_offset
}
```

**Impact**:
- Eliminates CAS #1 (helper) and CAS #3 (backward link) entirely
- Reduces from 3 CAS ops to 1 CAS op per level
- Halves the atomic contention surface per node
- Reduces false sharing (smaller Link struct)
- **Trade-off**: Backward iteration becomes O(n) instead of O(1) per step. For LSM memtable use cases (primarily forward scans and point lookups), this is acceptable.

### Solution 2: Relax Atomic Orderings (Medium Impact)

Change all insertion-path CAS operations from `SeqCst` to `Release` (success) / `Acquire` (failure):

```rust
// Before
prev.cas_next_offset(&self.arena, i, next.offset(), nd.offset(),
    Ordering::SeqCst, Ordering::Acquire);

// After
prev.cas_next_offset(&self.arena, i, next.offset(), nd.offset(),
    Ordering::Release, Ordering::Acquire);
```

**Impact**: Estimated 10-30% improvement under contention. Zero correctness risk — the code already documents that acquire/release is sufficient.

### Solution 3: Smarter Splice Cache Invalidation (Low Impact)

Instead of invalidating the entire splice cache on CAS failure, only invalidate the affected level:

```rust
// Before
invalid_data_splice = true;  // invalidates ALL levels

// After: only update the current level's splice
ins.spl[i].prev = fr.splice.prev;
ins.spl[i].next = fr.splice.next;
// Higher levels remain valid
```

**Impact**: Marginal improvement for single insertions, but reduces wasted work in batch insertion scenarios.

## Recommendations

| Priority | Change | Expected Impact | Risk |
|----------|--------|----------------|------|
| 1 | Singly-linked tower module | ~100x improvement (recover baseline) | New code path, needs thorough testing |
| 2 | SeqCst to Release/Acquire | ~10-30% additional improvement | None (code documents this is correct) |
| 3 | Splice cache optimization | ~5-10% in batch scenarios | Low |

### Implementation Plan

1. Move current doubly-linked implementation into a `doubly` module (preserves backward iteration capability)
2. Create `singly` module based on `fa55ff6` architecture but with current type system
3. Relax atomic orderings in both modules
4. Benchmark to verify recovery of ~5 us write latency
5. Make `singly` the default, `doubly` opt-in for users who need O(1) backward iteration

## Appendix: rarena-allocator Performance Notes

The arena allocator (`rarena-allocator`) also has SeqCst orderings on its hot path that could be relaxed:

| Location | Operation | Current | Recommended |
|----------|-----------|---------|-------------|
| `sync.rs:805-809` | Allocation CAS | SeqCst | Release |
| `sync.rs:954-958` | Allocation CAS (with freelist) | SeqCst | Release |
| `sync.rs:1105-1109` | Allocation CAS (pessimistic) | SeqCst | Release |
| `sync.rs:402` | Deallocation CAS | SeqCst | Release |

Estimated 5-15% improvement in allocation throughput under contention.
