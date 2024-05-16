# CHANGELOG

## 0.10.0

- Add `upsert` and `upsert_with` methods to allow users update the old value when the key and version are the same.
- Add `remove` method to allow users remove the entry with the key but require version is not equal.
- Add `upremove` method to allow users remove the entry with same key and version.

## 0.9.0

- Make file backed mmap `SkipMap` and `SkipSet` still can be reopened even last time the program was aborted.
- Remove checksum validation, users should take care of data integrity by themselves.
- Support `Clone` directly, no need to use `Arc` wrapper anymore.
- Add `OpenOptions` and `MmapOptions` to support better controls on file mmap backed `SkipMap` and `SkipSet`.

## 0.8.6

- Add `SkipMap::min_version` and `SkipSet::min_version` to access the min version of the `SkipMap` or `SkipSet`.
- Fix `max_version` is not be updated when using `SkipMap::insert_with`.

## 0.8.5

- Add accessor to `Comparator`.

## 0.8.4

- Relax `MapIterator` and `SetIterator` trait bound
- Add `SkipMap::max_version` and `SkipSet::max_version` to access the max version of the `SkipMap` or `SkipSet`.
- Add checksum and max version in overhead for memmory mapped backend `SkipMap` or `SkipSet`.
- Use CAS instead of `fetch_update` in `Arena::alloc`.

## 0.8.3

- Make the result of `MapIterator::entry` and `SetIterator::entry` reference to `'a`

## 0.8.2

- Make the result of `MapIterator::seek_upper_bound` and `MapIterator::seek_lower_bound` reference to `'a`
- Make the result of `SetIterator::seek_upper_bound` and `SetIterator::seek_lower_bound` reference to `'a`

## 0.8.1

- Add `entry` method for `MapIterator` and `SetIterator` to support access the last yield entry of the iterator.

## 0.8.0

- Make `SkipMap::insert` and `SkipSet::insert` return the current value if the key and trailer already exist.
- Add the `SkipMap::insert_with` method to support inserting an occupied key first, then write the value in the closure semantic.

## 0.7.0

- Implement `Iterator` for `MapIterator` and `SetIterator`.
- Optimize `Arena::alloc` logic.

## 0.6.0

- Change mmap related API
- Support open exist `SkipMap` and `SkipSet` file in read only mode.

## 0.5.1

- Add `flush` API

## UNRELEASED

FEATURES
