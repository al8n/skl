# CHANGELOG

## 0.22

- Improve the flexibility of generic version `SkipMap`

## 0.21

- Use state pattern for `EntryRef`

## 0.20

- Add dynamic `SkipMap`s
- Support create multiple `SkipMap`s on the same `Allocator`
- Improve docs on some constructor methods

## 0.19

- Cleanup structures and remove `Trailer`, `TrailedMap` and `FullMap`
- Add `version` guard for query APIs
- Add `Height::with` and `KeySize::with`
- Fix wrong result returned from `Key::is_remove`
- Add `data_offset` and `data_offset_unify` method for `Options`
- Renaming types

## 0.17

- Refactor to support generic key-value types
- Fix `DoubleEndIterator` implementation
- Lazy init the `V::Ref<'a>` and `K::Ref<'a>` in `EntryRef`

## 0.15

- Extract different kinds of `SkipMap` to traits to improve flexibility
- Implementing a builder pattern to construct `SkipMap`s
- Make the crate compatible with [Tree Borrows](https://www.ralfj.de/blog/2023/06/02/tree-borrows.html)

## 0.14

- Supports unsync version `SkipMap`s
- Fix: dealloc potential in-unsed memory chunk
- Add `CompressionPolicy` as a configuration
- Increase the discarded tracker when find new version of a key

## 0.13

- Remove `Comparator` generic on `Entry*`

## 0.12

- Bump `rarena-allocator`'s version
- Change value callback from `impl FnOnce + Copy` to `impl Fn`

## 0.11

- Refactor and extract lock-free ARENA allocator implementation to [`rarena-allocator`](https://github.com/al8n/rarena) crate.
  - Add an ordered linked list to track segments.
- Increase maximum key size to `u27::MAX`
- Support key prefix compression
- Support version compatibility check
- Add `Options` as a parameter when constructing the `SkipMap` and `SkipSet`
  - Support specify max key size and max value size
  - Support set the max height

## 0.10

- Remove `SkipSet`
- Add `insert`, `insert_with`, `insert_with_value`, `get_or_insert`, `get_or_insert` and `get_or_insert_with_value` methods
- Add `compare_remove`, `get_or_remove` and `get_or_remove_with` methods
- Add `Entry` and `VersionedEntry`
- Add discard states tracker and `discarded` method to let users know how many bytes in ARENA are discarded.
- Rename `OccupiedValue` to `VacantBuffer` and do not panic when users do not fully fill `VacantBuffer`
- Add `tracing`
- Add `SkipMap::refs` API to allow users get how many references.

## 0.9

- Make file backed mmap `SkipMap` and `SkipSet` still can be reopened even last time the program was aborted.
- Remove checksum validation, users should take care of data integrity by themselves.
- Support `Clone` directly, no need to use `Arc` wrapper anymore.
- Add `OpenOptions` and `MmapOptions` to support better controls on file mmap backed `SkipMap` and `SkipSet`.

## 0.8.6

- Add `SkipMap::minimum_version` and `SkipSet::minimum_version` to access the min version of the `SkipMap` or `SkipSet`.
- Fix `maximum_version` is not be updated when using `SkipMap::insert_with`.

## 0.8.5

- Add accessor to `Comparator`.

## 0.8.4

- Relax `MapIterator` and `SetIterator` trait bound
- Add `SkipMap::maximum_version` and `SkipSet::maximum_version` to access the max version of the `SkipMap` or `SkipSet`.
- Add checksum and max version in overhead for memmory mapped backend `SkipMap` or `SkipSet`.
- Use CAS instead of `fetch_update` in `Arena::alloc`.

## 0.8.3

- Make the result of `MapIterator::entry` and `SetIterator::entry` reference to `'a`

## 0.8.2

- Make the result of `MapIterator::seek_upper_bound` and `MapIterator::seek_lower_bound` reference to `'a`
- Make the result of `SetIterator::seek_upper_bound` and `SetIterator::seek_lower_bound` reference to `'a`

## 0.8.1

- Add `entry` method for `MapIterator` and `SetIterator` to support access the last yield entry of the iterator.

## 0.8

- Make `SkipMap::insert` and `SkipSet::insert` return the current value if the key and trailer already exist.
- Add the `SkipMap::insert_with` method to support inserting an vacant key first, then write the value in the closure semantic.

## 0.7

- Implement `Iterator` for `MapIterator` and `SetIterator`.
- Optimize `Arena::alloc` logic.

## 0.6

- Change mmap related API
- Support open exist `SkipMap` and `SkipSet` file in read only mode.

## 0.5.1

- Add `flush` API

## UNRELEASED
