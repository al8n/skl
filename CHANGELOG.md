# CHANGELOG

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
