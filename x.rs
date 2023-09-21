#![feature(prelude_import)]
//!<div align="center">
//!    <h1>SKL</h1>
//!</div>
//!
//!<div align="center">
//!
//![<img alt="github" src="https://img.shields.io/badge/github-al8n/skl-8da0cb?style=for-the-badge&logo=Github" height="22">][Github-url]
//![<img alt="Build" src="https://img.shields.io/github/actions/workflow/status/al8n/skl-rs/ci.yml?style=for-the-badge&logo=Github-Actions&label=CI" height="22">][CI-url]
//![<img alt="codecov" src="https://img.shields.io/codecov/c/gh/al8n/skl-rs?style=for-the-badge&token=aek5JwyaAZ&logo=codecov" height="22">][codecov-url]
//!
//![<img alt="docs.rs" src="https://img.shields.io/badge/docs.rs-skl-66c2a5?style=for-the-badge&labelColor=555555&logo=data:image/svg+xml;base64,PHN2ZyByb2xlPSJpbWciIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyIgdmlld0JveD0iMCAwIDUxMiA1MTIiPjxwYXRoIGZpbGw9IiNmNWY1ZjUiIGQ9Ik00ODguNiAyNTAuMkwzOTIgMjE0VjEwNS41YzAtMTUtOS4zLTI4LjQtMjMuNC0zMy43bC0xMDAtMzcuNWMtOC4xLTMuMS0xNy4xLTMuMS0yNS4zIDBsLTEwMCAzNy41Yy0xNC4xIDUuMy0yMy40IDE4LjctMjMuNCAzMy43VjIxNGwtOTYuNiAzNi4yQzkuMyAyNTUuNSAwIDI2OC45IDAgMjgzLjlWMzk0YzAgMTMuNiA3LjcgMjYuMSAxOS45IDMyLjJsMTAwIDUwYzEwLjEgNS4xIDIyLjEgNS4xIDMyLjIgMGwxMDMuOS01MiAxMDMuOSA1MmMxMC4xIDUuMSAyMi4xIDUuMSAzMi4yIDBsMTAwLTUwYzEyLjItNi4xIDE5LjktMTguNiAxOS45LTMyLjJWMjgzLjljMC0xNS05LjMtMjguNC0yMy40LTMzLjd6TTM1OCAyMTQuOGwtODUgMzEuOXYtNjguMmw4NS0zN3Y3My4zek0xNTQgMTA0LjFsMTAyLTM4LjIgMTAyIDM4LjJ2LjZsLTEwMiA0MS40LTEwMi00MS40di0uNnptODQgMjkxLjFsLTg1IDQyLjV2LTc5LjFsODUtMzguOHY3NS40em0wLTExMmwtMTAyIDQxLjQtMTAyLTQxLjR2LS42bDEwMi0zOC4yIDEwMiAzOC4ydi42em0yNDAgMTEybC04NSA0Mi41di03OS4xbDg1LTM4Ljh2NzUuNHptMC0xMTJsLTEwMiA0MS40LTEwMi00MS40di0uNmwxMDItMzguMiAxMDIgMzguMnYuNnoiPjwvcGF0aD48L3N2Zz4K" height="20">][doc-url]
//![<img alt="crates.io" src="https://img.shields.io/crates/v/skl?style=for-the-badge&logo=data:image/svg+xml;base64,PD94bWwgdmVyc2lvbj0iMS4wIiBlbmNvZGluZz0iaXNvLTg4NTktMSI/Pg0KPCEtLSBHZW5lcmF0b3I6IEFkb2JlIElsbHVzdHJhdG9yIDE5LjAuMCwgU1ZHIEV4cG9ydCBQbHVnLUluIC4gU1ZHIFZlcnNpb246IDYuMDAgQnVpbGQgMCkgIC0tPg0KPHN2ZyB2ZXJzaW9uPSIxLjEiIGlkPSJMYXllcl8xIiB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHhtbG5zOnhsaW5rPSJodHRwOi8vd3d3LnczLm9yZy8xOTk5L3hsaW5rIiB4PSIwcHgiIHk9IjBweCINCgkgdmlld0JveD0iMCAwIDUxMiA1MTIiIHhtbDpzcGFjZT0icHJlc2VydmUiPg0KPGc+DQoJPGc+DQoJCTxwYXRoIGQ9Ik0yNTYsMEwzMS41MjgsMTEyLjIzNnYyODcuNTI4TDI1Niw1MTJsMjI0LjQ3Mi0xMTIuMjM2VjExMi4yMzZMMjU2LDB6IE0yMzQuMjc3LDQ1Mi41NjRMNzQuOTc0LDM3Mi45MTNWMTYwLjgxDQoJCQlsMTU5LjMwMyw3OS42NTFWNDUyLjU2NHogTTEwMS44MjYsMTI1LjY2MkwyNTYsNDguNTc2bDE1NC4xNzQsNzcuMDg3TDI1NiwyMDIuNzQ5TDEwMS44MjYsMTI1LjY2MnogTTQzNy4wMjYsMzcyLjkxMw0KCQkJbC0xNTkuMzAzLDc5LjY1MVYyNDAuNDYxbDE1OS4zMDMtNzkuNjUxVjM3Mi45MTN6IiBmaWxsPSIjRkZGIi8+DQoJPC9nPg0KPC9nPg0KPGc+DQo8L2c+DQo8Zz4NCjwvZz4NCjxnPg0KPC9nPg0KPGc+DQo8L2c+DQo8Zz4NCjwvZz4NCjxnPg0KPC9nPg0KPGc+DQo8L2c+DQo8Zz4NCjwvZz4NCjxnPg0KPC9nPg0KPGc+DQo8L2c+DQo8Zz4NCjwvZz4NCjxnPg0KPC9nPg0KPGc+DQo8L2c+DQo8Zz4NCjwvZz4NCjxnPg0KPC9nPg0KPC9zdmc+DQo=" height="22">][crates-url]
//!<img alt="license" src="https://img.shields.io/badge/License-Apache%202.0/MIT-blue.svg?style=for-the-badge&fontColor=white&logoColor=f5c076&logo=data:image/svg+xml;base64,PCFET0NUWVBFIHN2ZyBQVUJMSUMgIi0vL1czQy8vRFREIFNWRyAxLjEvL0VOIiAiaHR0cDovL3d3dy53My5vcmcvR3JhcGhpY3MvU1ZHLzEuMS9EVEQvc3ZnMTEuZHRkIj4KDTwhLS0gVXBsb2FkZWQgdG86IFNWRyBSZXBvLCB3d3cuc3ZncmVwby5jb20sIFRyYW5zZm9ybWVkIGJ5OiBTVkcgUmVwbyBNaXhlciBUb29scyAtLT4KPHN2ZyBmaWxsPSIjZmZmZmZmIiBoZWlnaHQ9IjgwMHB4IiB3aWR0aD0iODAwcHgiIHZlcnNpb249IjEuMSIgaWQ9IkNhcGFfMSIgeG1sbnM9Imh0dHA6Ly93d3cudzMub3JnLzIwMDAvc3ZnIiB4bWxuczp4bGluaz0iaHR0cDovL3d3dy53My5vcmcvMTk5OS94bGluayIgdmlld0JveD0iMCAwIDI3Ni43MTUgMjc2LjcxNSIgeG1sOnNwYWNlPSJwcmVzZXJ2ZSIgc3Ryb2tlPSIjZmZmZmZmIj4KDTxnIGlkPSJTVkdSZXBvX2JnQ2FycmllciIgc3Ryb2tlLXdpZHRoPSIwIi8+Cg08ZyBpZD0iU1ZHUmVwb190cmFjZXJDYXJyaWVyIiBzdHJva2UtbGluZWNhcD0icm91bmQiIHN0cm9rZS1saW5lam9pbj0icm91bmQiLz4KDTxnIGlkPSJTVkdSZXBvX2ljb25DYXJyaWVyIj4gPGc+IDxwYXRoIGQ9Ik0xMzguMzU3LDBDNjIuMDY2LDAsMCw2Mi4wNjYsMCwxMzguMzU3czYyLjA2NiwxMzguMzU3LDEzOC4zNTcsMTM4LjM1N3MxMzguMzU3LTYyLjA2NiwxMzguMzU3LTEzOC4zNTcgUzIxNC42NDgsMCwxMzguMzU3LDB6IE0xMzguMzU3LDI1OC43MTVDNzEuOTkyLDI1OC43MTUsMTgsMjA0LjcyMywxOCwxMzguMzU3UzcxLjk5MiwxOCwxMzguMzU3LDE4IHMxMjAuMzU3LDUzLjk5MiwxMjAuMzU3LDEyMC4zNTdTMjA0LjcyMywyNTguNzE1LDEzOC4zNTcsMjU4LjcxNXoiLz4gPHBhdGggZD0iTTE5NC43OTgsMTYwLjkwM2MtNC4xODgtMi42NzctOS43NTMtMS40NTQtMTIuNDMyLDIuNzMyYy04LjY5NCwxMy41OTMtMjMuNTAzLDIxLjcwOC0zOS42MTQsMjEuNzA4IGMtMjUuOTA4LDAtNDYuOTg1LTIxLjA3OC00Ni45ODUtNDYuOTg2czIxLjA3Ny00Ni45ODYsNDYuOTg1LTQ2Ljk4NmMxNS42MzMsMCwzMC4yLDcuNzQ3LDM4Ljk2OCwyMC43MjMgYzIuNzgyLDQuMTE3LDguMzc1LDUuMjAxLDEyLjQ5NiwyLjQxOGM0LjExOC0yLjc4Miw1LjIwMS04LjM3NywyLjQxOC0xMi40OTZjLTEyLjExOC0xNy45MzctMzIuMjYyLTI4LjY0NS01My44ODItMjguNjQ1IGMtMzUuODMzLDAtNjQuOTg1LDI5LjE1Mi02NC45ODUsNjQuOTg2czI5LjE1Miw2NC45ODYsNjQuOTg1LDY0Ljk4NmMyMi4yODEsMCw0Mi43NTktMTEuMjE4LDU0Ljc3OC0zMC4wMDkgQzIwMC4yMDgsMTY5LjE0NywxOTguOTg1LDE2My41ODIsMTk0Ljc5OCwxNjAuOTAzeiIvPiA8L2c+IDwvZz4KDTwvc3ZnPg==" height="22">
//!
//!1. A lock-free thread-safe concurrent ARENA based skiplist implementation which helps develop MVCC memtable for LSM-Tree.
//!2. A lock-free thread-safe concurrent memory map based on-disk skiplist.
//!
//!Inspired by [Dgraph's badger](https://github.com/dgraph-io/badger/tree/main/skl).
//!
//!</div>
//!
//!## Installation
//!
//!- Only use heap backend (suppport `no_std`)
//!  
//!    ```toml
//!    [dependencies]
//!    skl = "0.4-alpha.1"
//!    ```
//!
//!- Enable memory map backend
//!
//!    ```toml
//!    [dependencies]
//!    skl = { version = "0.4.0-alpha.1", features = ["mmap"] }
//!    ```
//!
//!## Examples
//!
//!Please see [examples](https://github.com/al8n/skl-rs/tree/main/examples) folder for more details.
//!
//!## Tests
//!
//!- `test`:
//!
//!    ```sh
//!    cargo test --all-features
//!    ```
//!
//!- `miri`:
//!
//!    ```sh
//!    cargo miri test --all-features
//!    ```
//!
//!## Support Platforms
//!
//!| targets                       |   status  |
//!|:-----------------------------:|:---------:|
//!| aarch64-linux-android         |  &#9989;  |
//!| aarch64-unknown-linux-gnu     |  &#9989;  |
//!| aarch64-unknown-linux-musl    |  &#9989;  |
//!| i686-pc-windows-gnu           |  &#9989;  |
//!| i686-linux-android            |  &#9989;  |
//!| i686-unknown-linux-gnu        |  &#9989;  |
//!| mips64-unknown-linux-gnuabi64 |  &#9989;  |
//!| powerpc64-unknown-linux-gnu   |  &#9989;  |
//!| riscv64gc-unknown-linux-gnu   |  &#9989;  |
//!| wasm32-unknown-unknown        |  &#9989;  |
//!| wasm32-unknown-emscripten     |  &#9989;  |
//!| x86_64-unknown-linux-gnu      |  &#9989;  |
//!| x86_64-pc-windows-gnu         |  &#9989;  |
//!| x86_64-linux-android          |  &#9989;  |
//!
//!## TODO (help wanted)
//!
//!- [x] make the crate test cases pass `cargo miri`
//!- [ ] make the crate test cases pass `cargo loom`
//!- [ ] Implement
//!  - [ ] `get_or_insert`
//!  - [ ] `remove`
//!  - [ ] `contains`
//!  - [ ] change signature from `insert(k, v)` => `insert(k, v) -> Option<ValueRef>`
//!  - [x] mmap backend (currently is vector backend)
//!  - [ ] Supports `SkipSet`
//!
//!
//!#### License
//!
//!`skl-rs` is under the terms of both the MIT license and the
//!Apache License (Version 2.0).
//!
//!See [LICENSE-APACHE](LICENSE-APACHE), [LICENSE-MIT](LICENSE-MIT) for details.
//!
//!Copyright (c) 2022 Al Liu.
//!
//![Github-url]: https://github.com/al8n/skl-rs/
//![CI-url]: https://github.com/al8n/skl-rs/actions/workflows/ci.yml
//![doc-url]: https://docs.rs/skl
//![crates-url]: https://crates.io/crates/skl
//![codecov-url]: https://app.codecov.io/gh/al8n/skl-rs/
//![rustc-url]: https://github.com/rust-lang/rust/blob/master/RELEASES.md
//![license-apache-url]: https://opensource.org/licenses/Apache-2.0
//![license-mit-url]: https://opensource.org/licenses/MIT
#![deny(missing_docs)]
#[prelude_import]
use std::prelude::rust_2021::*;
#[macro_use]
extern crate std;
extern crate alloc;
#[cfg(feature = "std")]
extern crate std;
mod error {
    /// Error type for the skl crate.
    pub enum Error {
        /// Indicates that the arena is full and cannot perform any more
        /// allocations.
        #[error("allocation failed because arena is full")]
        Full,
        /// Indicates that an entry with the specified key already
        /// exists in the skiplist. As a low-level crate, duplicate entries are not directly supported and
        /// instead must be handled by the user.
        #[error("key already exists in the skiplist")]
        Duplicated,
    }
    #[allow(unused_qualifications)]
    impl std::error::Error for Error {}
    #[allow(unused_qualifications)]
    impl std::fmt::Display for Error {
        fn fmt(&self, __formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
            #[allow(unused_variables, deprecated, clippy::used_underscore_binding)]
            match self {
                Error::Full {} => {
                    __formatter.write_fmt(format_args!("allocation failed because arena is full"))
                }
                Error::Duplicated {} => {
                    __formatter.write_fmt(format_args!("key already exists in the skiplist"))
                }
            }
        }
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for Error {
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::write_str(
                f,
                match self {
                    Error::Full => "Full",
                    Error::Duplicated => "Duplicated",
                },
            )
        }
    }
}
pub use error::Error;
mod value {
    use crate::Trailer;
    /// Gives the users the ability to define their own value type, rather than just slice.
    ///
    /// For a value-value database, the value inserted by the end-users will always be encoded to a u8 array.
    /// But the value-value database developers are tend to add some extra information
    /// to the value provided by the end-users.
    /// e.g. ttl, version, tombstones, and etc.
    ///
    /// This trait gives the value-value database developers the ability to add extra information
    /// to the value provided by the end-users by associated type [`Trailer`](crate::Trailer).
    ///
    /// # Example
    ///
    /// 1. The [`InternalValue`](https://github.com/cockroachdb/pebble/blob/master/internal/base/internal.go#L171) of [cockroachdb's pebble](https://github.com/cockroachdb/pebble) can be implemented by using this trait as:
    ///
    ///     ```rust,no_run
    ///     #[repr(u64)]
    ///     enum InternalValueVind {
    ///       Delete,
    ///       Set,
    ///       Merge,
    ///       LogData,
    ///       // ...
    ///     }
    ///
    ///     #[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
    ///     #[repr(transparent)]
    ///     struct PebbleValueTrailer(u64);
    ///
    ///     impl skl::Trailer for PebbleValueTrailer {
    ///       fn encoded_size(&self) -> usize {
    ///         core::mem::size_of::<u64>()
    ///       }
    ///
    ///       fn encode(&self, buf: &mut [u8]) {
    ///         buf.copy_from_slice(&self.0.to_le_bytes());
    ///       }
    ///
    ///       fn decode(src: &[u8]) -> Self {
    ///         Self(u64::from_le_bytes(src[..core::mem::size_of::<u64>()].try_into().unwrap()))
    ///       }
    ///     }
    ///
    ///     impl PebbleValueTrailer {
    ///       fn make_trailer(seq_num: u64, kind: InternalValueVind) -> u64 {
    ///         (seq_num << 8) | (kind as u64)
    ///       }
    ///
    ///       fn seq_num(&self) -> u64 {
    ///         self.0 >> 8
    ///       }
    ///     }
    ///
    ///     struct PebbleValue {
    ///       user_value: Vec<u8>,
    ///       trailer: PebbleValueTrailer,
    ///     }
    ///
    ///     impl skl::Value for PebbleValue {
    ///       type Trailer = PebbleValueTrailer;
    ///       
    ///       fn as_bytes(&self) -> &[u8] {
    ///         self.user_value.as_slice()
    ///       }
    ///
    ///       fn trailer(&self) -> &Self::Trailer {
    ///         &self.trailer
    ///       }
    ///     }
    ///     ```
    ///
    /// 2. The [`Value`]() of [dgraph's badger](https://github.com/dgraph-io/badger) can be implemented by using this trait as:
    ///   
    ///     ```rust,no_run
    ///
    ///     struct BadgerValue {
    ///       timestamp: u64,
    ///       data: Vec<u8>,
    ///     }
    ///   
    ///     impl skl::Value for BadgerValue {
    ///       type Trailer = u64;
    ///
    ///       fn as_bytes(&self) -> &[u8] {
    ///         self.data.as_slice()
    ///       }
    ///
    ///       fn trailer(&self) -> &Self::Trailer {
    ///         &self.timestamp
    ///       }
    ///     }
    ///     ```
    pub trait Value {
        /// Extra information should be added for the value provided by end-users.
        type Trailer: Trailer;
        #[doc(hidden)]
        const _TRAILER_CHECV: () = {
            if !(core::mem::align_of::<Self::Trailer>() % 4 == 0) {
                {
                    ::core::panicking::panic_fmt(format_args!(
                        "The alignment of the trailer type must be a multiple of 4"
                    ));
                }
            };
        };
        /// Returns the bytes of the value without the trailer.
        fn as_bytes(&self) -> &[u8];
        /// Returns the trailer of the value.
        fn trailer(&self) -> &Self::Trailer;
    }
    impl Value for Vec<u8> {
        type Trailer = ();
        #[inline]
        fn as_bytes(&self) -> &[u8] {
            self.as_slice()
        }
        #[inline]
        fn trailer(&self) -> &Self::Trailer {
            &()
        }
    }
    impl Value for Box<[u8]> {
        type Trailer = ();
        #[inline]
        fn as_bytes(&self) -> &[u8] {
            self.as_ref()
        }
        #[inline]
        fn trailer(&self) -> &Self::Trailer {
            &()
        }
    }
    impl Value for ::alloc::sync::Arc<[u8]> {
        type Trailer = ();
        #[inline]
        fn as_bytes(&self) -> &[u8] {
            self.as_ref()
        }
        #[inline]
        fn trailer(&self) -> &Self::Trailer {
            &()
        }
    }
    impl<const N: usize> Value for [u8; N] {
        type Trailer = ();
        #[inline]
        fn as_bytes(&self) -> &[u8] {
            self.as_ref()
        }
        #[inline]
        fn trailer(&self) -> &Self::Trailer {
            &()
        }
    }
    impl<'a> Value for &'a [u8] {
        type Trailer = ();
        #[inline]
        fn as_bytes(&self) -> &[u8] {
            self
        }
        #[inline]
        fn trailer(&self) -> &Self::Trailer {
            &()
        }
    }
    impl<'a> Value for &'a str {
        type Trailer = ();
        #[inline]
        fn as_bytes(&self) -> &[u8] {
            str::as_bytes(self)
        }
        #[inline]
        fn trailer(&self) -> &Self::Trailer {
            &()
        }
    }
    impl Value for String {
        type Trailer = ();
        #[inline]
        fn as_bytes(&self) -> &[u8] {
            self.as_bytes()
        }
        #[inline]
        fn trailer(&self) -> &Self::Trailer {
            &()
        }
    }
    #[cfg(feature = "bytes")]
    impl Value for bytes::Bytes {
        type Trailer = ();
        #[inline]
        fn as_bytes(&self) -> &[u8] {
            self.as_ref()
        }
        #[inline]
        fn trailer(&self) -> &Self::Trailer {
            &()
        }
    }
    /// The value reference
    pub struct ValueRef<'a, V: Value> {
        data: &'a [u8],
        trailer: &'a V::Trailer,
    }
    impl<'a, V: Value> ValueRef<'a, V> {
        /// Creates a new value reference directly from the given bytes and trailer.
        #[inline]
        pub const fn new(data: &'a [u8], trailer: &'a V::Trailer) -> Self {
            Self { data, trailer }
        }
        /// Returns the bytes of the value without the trailer.
        #[inline]
        pub const fn as_bytes(&self) -> &[u8] {
            self.data
        }
        /// Returns the trailer of the value.
        #[inline]
        pub const fn trailer(&self) -> &V::Trailer {
            self.trailer
        }
        /// Returns the encoded size of the value.
        #[inline]
        pub fn encoded_size(&self) -> usize {
            self.data.len()
        }
        /// Encodes the value into the given buffer. The buffer must be at least `self.encoded_size()` bytes.
        pub fn encode(&self, buf: &mut [u8]) {
            let value = self.as_bytes();
            let value_len = value.len();
            buf[..value_len].copy_from_slice(value);
        }
    }
    /// A trait for types that can be converted to a value reference. [`ValueRef`](crate::ValueRef) is the value used to insert to the skiplist.
    pub trait AsValueRef {
        /// The value type.
        type Value: Value;
        /// Converts the given value to a value reference.
        fn as_value_ref(&self) -> ValueRef<Self::Value>;
    }
    impl<V: Value> AsValueRef for V {
        type Value = V;
        #[inline]
        fn as_value_ref(&self) -> ValueRef<V> {
            ValueRef {
                data: self.as_bytes(),
                trailer: self.trailer(),
            }
        }
    }
}
pub use value::*;
mod key {
    use crate::Trailer;
    /// Gives the users the ability to define their own key type, rather than just slice.
    ///
    /// For a key-value database, the key inserted by the end-users will always be encoded to a u8 array.
    /// But the key-value database developers are tend to add some extra information
    /// to the key provided by the end-users.
    /// e.g. ttl, version, tombstones, and etc.
    ///
    /// This trait gives the key-value database developers the ability to add extra information
    /// to the key provided by the end-users by associated type [`Trailer`](crate::Trailer).
    ///
    /// # Example
    ///
    /// 1. The [`InternalKey`](https://github.com/cockroachdb/pebble/blob/master/internal/base/internal.go#L171) of [cockroachdb's pebble](https://github.com/cockroachdb/pebble) can be implemented by using this trait as:
    ///
    ///     ```rust,no_run
    ///     #[repr(u64)]
    ///     enum InternalKeyKind {
    ///       Delete,
    ///       Set,
    ///       Merge,
    ///       LogData,
    ///       // ...
    ///     }
    ///
    ///     #[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
    ///     #[repr(transparent)]
    ///     struct PebbleKeyTrailer(u64);
    ///
    ///     impl skl::Trailer for PebbleKeyTrailer {
    ///       fn encoded_size(&self) -> usize {
    ///         core::mem::size_of::<u64>()
    ///       }
    ///
    ///       fn encode(&self, buf: &mut [u8]) {
    ///         buf.copy_from_slice(&self.0.to_le_bytes());
    ///       }
    ///
    ///       fn decode(src: &[u8]) -> Self {
    ///         Self(u64::from_le_bytes(src[..core::mem::size_of::<u64>()].try_into().unwrap()))
    ///       }
    ///     }
    ///
    ///     impl PebbleKeyTrailer {
    ///       fn make_trailer(seq_num: u64, kind: InternalKeyKind) -> u64 {
    ///         (seq_num << 8) | (kind as u64)
    ///       }
    ///
    ///       fn seq_num(&self) -> u64 {
    ///         self.0 >> 8
    ///       }
    ///     }
    ///
    ///     struct PebbleKey {
    ///       user_key: Vec<u8>,
    ///       trailer: PebbleKeyTrailer,
    ///     }
    ///
    ///     impl skl::Key for PebbleKey {
    ///       type Trailer = PebbleKeyTrailer;
    ///       
    ///       fn as_bytes(&self) -> &[u8] {
    ///         self.user_key.as_slice()
    ///       }
    ///
    ///       fn trailer(&self) -> &Self::Trailer {
    ///         &self.trailer
    ///       }
    ///     }
    ///     ```
    ///
    /// 2. The [`Key`]() of [dgraph's badger](https://github.com/dgraph-io/badger) can be implemented by using this trait as:
    ///   
    ///     ```rust,no_run
    ///
    ///     struct BadgerKey {
    ///       timestamp: u64,
    ///       data: Vec<u8>,
    ///     }
    ///   
    ///     impl skl::Key for BadgerKey {
    ///       type Trailer = u64;
    ///
    ///       fn as_bytes(&self) -> &[u8] {
    ///         self.data.as_slice()
    ///       }
    ///
    ///       fn trailer(&self) -> &Self::Trailer {
    ///         &self.timestamp
    ///       }
    ///     }
    ///     ```
    pub trait Key {
        /// Extra information should be added for the key provided by end-users.
        type Trailer: Trailer;
        /// Returns the bytes of the key without the trailer.
        fn as_bytes(&self) -> &[u8];
        /// Returns the trailer of the key.
        fn trailer(&self) -> &Self::Trailer;
    }
    impl Key for Vec<u8> {
        type Trailer = ();
        #[inline]
        fn as_bytes(&self) -> &[u8] {
            self.as_slice()
        }
        #[inline]
        fn trailer(&self) -> &Self::Trailer {
            &()
        }
    }
    impl Key for Box<[u8]> {
        type Trailer = ();
        #[inline]
        fn as_bytes(&self) -> &[u8] {
            self.as_ref()
        }
        #[inline]
        fn trailer(&self) -> &Self::Trailer {
            &()
        }
    }
    impl Key for ::alloc::sync::Arc<[u8]> {
        type Trailer = ();
        #[inline]
        fn as_bytes(&self) -> &[u8] {
            self.as_ref()
        }
        #[inline]
        fn trailer(&self) -> &Self::Trailer {
            &()
        }
    }
    impl<const N: usize> Key for [u8; N] {
        type Trailer = ();
        #[inline]
        fn as_bytes(&self) -> &[u8] {
            self.as_ref()
        }
        #[inline]
        fn trailer(&self) -> &Self::Trailer {
            &()
        }
    }
    impl<'a> Key for &'a [u8] {
        type Trailer = ();
        #[inline]
        fn as_bytes(&self) -> &[u8] {
            self
        }
        #[inline]
        fn trailer(&self) -> &Self::Trailer {
            &()
        }
    }
    impl<'a> Key for &'a str {
        type Trailer = ();
        #[inline]
        fn as_bytes(&self) -> &[u8] {
            str::as_bytes(self)
        }
        #[inline]
        fn trailer(&self) -> &Self::Trailer {
            &()
        }
    }
    impl Key for String {
        type Trailer = ();
        #[inline]
        fn as_bytes(&self) -> &[u8] {
            self.as_bytes()
        }
        #[inline]
        fn trailer(&self) -> &Self::Trailer {
            &()
        }
    }
    #[cfg(feature = "bytes")]
    impl Key for bytes::Bytes {
        type Trailer = ();
        #[inline]
        fn as_bytes(&self) -> &[u8] {
            self.as_ref()
        }
        #[inline]
        fn trailer(&self) -> &Self::Trailer {
            &()
        }
    }
    /// The key reference
    pub struct KeyRef<'a, K: Key> {
        data: &'a [u8],
        trailer: &'a K::Trailer,
    }
    impl<'a, K: Key> KeyRef<'a, K> {
        /// Creates a new key reference directly from the given bytes and trailer.
        #[inline]
        pub const fn new(data: &'a [u8], trailer: &'a K::Trailer) -> Self {
            Self { data, trailer }
        }
        /// Returns the bytes of the key without the trailer.
        #[inline]
        pub const fn as_bytes(&self) -> &[u8] {
            self.data
        }
        /// Returns the trailer of the key.
        #[inline]
        pub const fn trailer(&self) -> &K::Trailer {
            self.trailer
        }
        /// Returns the encoded size of the key.
        #[inline]
        pub fn encoded_size(&self) -> usize {
            self.data.len()
        }
        /// Encodes the key into the given buffer. The buffer must be at least `self.encoded_size()` bytes.
        pub fn encode(&self, buf: &mut [u8]) {
            let key = self.as_bytes();
            let key_len = key.len();
            buf[..key_len].copy_from_slice(key);
        }
    }
    /// A trait for types that can be converted to a key reference. [`KeyRef`](crate::KeyRef) is the key used to insert to the skiplist.
    pub trait AsKeyRef {
        /// The key type.
        type Key: Key;
        /// Converts the given key to a key reference.
        fn as_key_ref(&self) -> KeyRef<Self::Key>;
    }
    impl<K: Key> AsKeyRef for K {
        type Key = K;
        #[inline]
        fn as_key_ref(&self) -> KeyRef<K> {
            KeyRef {
                data: self.as_bytes(),
                trailer: self.trailer(),
            }
        }
    }
}
pub use key::*;
mod map2 {
    use core::{ptr, cmp};
    use crossbeam_utils::CachePadded;
    use crate::{
        sync::{AtomicU32, Ordering},
        Comparator,
        error::Error,
        Key, KeyRef, Value,
    };
    mod arena {
        use crate::{
            error::Error,
            sync::{AtomicMut, AtomicPtr, Ordering},
            Key, Value,
        };
        use ::alloc::boxed::Box;
        use core::{
            ptr::{self, NonNull},
            slice,
            sync::atomic::AtomicU64,
            mem,
        };
        use crossbeam_utils::CachePadded;
        use super::node::{Node, Link};
        mod shared {
            use ::alloc::alloc;
            use core::{
                ops::{Index, IndexMut},
                ptr, slice,
            };
            use crate::sync::AtomicUsize;
            struct AlignedVec {
                ptr: ptr::NonNull<u8>,
                cap: usize,
                len: usize,
            }
            #[automatically_derived]
            impl ::core::fmt::Debug for AlignedVec {
                fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                    ::core::fmt::Formatter::debug_struct_field3_finish(
                        f,
                        "AlignedVec",
                        "ptr",
                        &self.ptr,
                        "cap",
                        &self.cap,
                        "len",
                        &&self.len,
                    )
                }
            }
            impl Drop for AlignedVec {
                #[inline]
                fn drop(&mut self) {
                    if self.cap != 0 {
                        unsafe {
                            alloc::dealloc(self.ptr.as_ptr(), self.layout());
                        }
                    }
                }
            }
            impl AlignedVec {
                const ALIGNMENT: usize = 4;
                const MAX_CAPACITY: usize = isize::MAX as usize - (Self::ALIGNMENT - 1);
                #[inline]
                fn new(capacity: usize) -> Self {
                    if !(capacity <= Self::MAX_CAPACITY) {
                        {
                            ::core::panicking::panic_fmt(format_args!(
                                "`capacity` cannot exceed isize::MAX - {0}",
                                Self::ALIGNMENT - 1
                            ));
                        }
                    };
                    let ptr = unsafe {
                        let layout =
                            alloc::Layout::from_size_align_unchecked(capacity, Self::ALIGNMENT);
                        let ptr = alloc::alloc(layout);
                        if ptr.is_null() {
                            alloc::handle_alloc_error(layout);
                        }
                        ptr::NonNull::new_unchecked(ptr)
                    };
                    unsafe {
                        core::ptr::write_bytes(ptr.as_ptr(), 0, capacity);
                    }
                    Self {
                        ptr,
                        cap: capacity,
                        len: capacity,
                    }
                }
                #[inline]
                fn layout(&self) -> alloc::Layout {
                    unsafe { alloc::Layout::from_size_align_unchecked(self.cap, Self::ALIGNMENT) }
                }
                #[inline]
                fn as_mut_ptr(&mut self) -> *mut u8 {
                    self.ptr.as_ptr()
                }
                #[inline]
                const fn as_slice(&self) -> &[u8] {
                    unsafe { slice::from_raw_parts(self.ptr.as_ptr(), self.len) }
                }
                #[inline]
                fn as_mut_slice(&mut self) -> &mut [u8] {
                    unsafe { slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len) }
                }
            }
            impl<I: slice::SliceIndex<[u8]>> Index<I> for AlignedVec {
                type Output = <I as slice::SliceIndex<[u8]>>::Output;
                #[inline]
                fn index(&self, index: I) -> &Self::Output {
                    &self.as_slice()[index]
                }
            }
            impl<I: slice::SliceIndex<[u8]>> IndexMut<I> for AlignedVec {
                #[inline]
                fn index_mut(&mut self, index: I) -> &mut Self::Output {
                    &mut self.as_mut_slice()[index]
                }
            }
            enum SharedBackend {
                Vec(AlignedVec),
            }
            pub(super) struct Shared {
                pub(super) refs: AtomicUsize,
                cap: usize,
                backend: SharedBackend,
            }
            impl Shared {
                pub(super) fn new_vec(cap: usize) -> Self {
                    let vec = AlignedVec::new(cap);
                    Self {
                        cap: vec.cap,
                        backend: SharedBackend::Vec(vec),
                        refs: AtomicUsize::new(1),
                    }
                }
                pub(super) fn as_mut_ptr(&mut self) -> *mut u8 {
                    match &mut self.backend {
                        SharedBackend::Vec(vec) => vec.as_mut_ptr(),
                    }
                }
                #[inline]
                pub(super) const fn cap(&self) -> usize {
                    self.cap
                }
                /// Only works on mmap with a file backend, unmounts the memory mapped file and truncates it to the specified size.
                ///
                /// ## Safety:
                /// - This method must be invoked in the drop impl of `Arena`.
                pub(super) unsafe fn unmount(&mut self, size: usize) {}
            }
        }
        use shared::Shared;
        /// Arena should be lock-free
        pub struct Arena {
            data_ptr: NonNull<u8>,
            n: CachePadded<AtomicU64>,
            inner: AtomicPtr<()>,
            cap: usize,
        }
        impl core::fmt::Debug for Arena {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                let allocated = self.size();
                let data = unsafe { slice::from_raw_parts(self.data_ptr.as_ptr(), allocated) };
                f.debug_struct("Arena")
                    .field("cap", &self.cap)
                    .field("allocated", &allocated)
                    .field("data", &data)
                    .finish()
            }
        }
        impl Arena {
            /// Returns the number of bytes allocated by the arena.
            #[inline]
            pub fn size(&self) -> usize {
                self.n.load(Ordering::Acquire) as usize
            }
            /// Returns the capacity of the arena.
            #[inline]
            pub const fn capacity(&self) -> usize {
                self.cap
            }
        }
        impl Arena {
            #[inline]
            const fn min_cap<K: Key, V: Value>() -> usize {
                (Node::<K, V>::MAX_NODE_SIZE * 2) as usize
            }
            #[inline]
            pub(super) fn new_vec<K: Key, V: Value>(n: usize) -> Self {
                Self::new(Shared::new_vec(n.max(Self::min_cap::<K, V>())))
            }
            #[inline]
            fn new(mut shared: Shared) -> Self {
                let data_ptr = unsafe { NonNull::new_unchecked(shared.as_mut_ptr()) };
                Self {
                    cap: shared.cap(),
                    inner: AtomicPtr::new(Box::into_raw(Box::new(shared)) as _),
                    data_ptr,
                    n: CachePadded::new(AtomicU64::new(1)),
                }
            }
            #[inline]
            pub(super) fn alloc(
                &self,
                size: u32,
                align: u32,
                overflow: u32,
            ) -> Result<(u32, u32), Error> {
                let orig_size = self.n.load(Ordering::Acquire);
                if orig_size > self.cap as u64 {
                    return Err(Error::Full);
                }
                let padded = size + align;
                let new_size = self.n.fetch_add(padded as u64, Ordering::AcqRel);
                if new_size + overflow as u64 > self.cap as u64 {
                    return Err(Error::Full);
                }
                let offset = (new_size as u32 - padded + align) & !align;
                Ok((offset, padded))
            }
            /// ## Safety:
            /// - The caller must make sure that `offset` must be less than the capacity of the arena.
            /// - The caller must make sure that `size` must be less than the capacity of the arena.
            /// - The caller must make sure that `offset + size` must be less than the capacity of the arena.
            #[inline]
            pub(super) unsafe fn get_bytes(&self, offset: usize, size: usize) -> &[u8] {
                if offset == 0 {
                    return &[];
                }
                let ptr = self.get_pointer(offset);
                slice::from_raw_parts(ptr, size)
            }
            /// ## Safety:
            /// - The caller must make sure that `offset` must be less than the capacity of the arena.
            /// - The caller must make sure that `size` must be less than the capacity of the arena.
            /// - The caller must make sure that `offset + size` must be less than the capacity of the arena.
            #[allow(clippy::mut_from_ref)]
            #[inline]
            pub(super) unsafe fn get_bytes_mut(&self, offset: usize, size: usize) -> &mut [u8] {
                if offset == 0 {
                    return &mut [];
                }
                let ptr = self.get_pointer_mut(offset);
                slice::from_raw_parts_mut(ptr, size)
            }
            /// ## Safety:
            /// - The caller must make sure that `ptr` must be less than the end bound of the arena.
            #[inline]
            pub(super) unsafe fn get_pointer_offset(&self, ptr: *const u8) -> usize {
                if ptr.is_null() {
                    return 0;
                }
                ptr.offset_from(self.data_ptr.as_ptr()) as usize
            }
            /// ## Safety:
            /// - The caller must make sure that `offset` must be less than the capacity of the arena.
            #[inline]
            pub(super) unsafe fn get_pointer(&self, offset: usize) -> *const u8 {
                if offset == 0 {
                    return ptr::null();
                }
                self.data_ptr.as_ptr().add(offset)
            }
            /// ## Safety:
            /// - The caller must make sure that `offset` must be less than the capacity of the arena.
            #[inline]
            pub(super) unsafe fn get_pointer_mut(&self, offset: usize) -> *mut u8 {
                if offset == 0 {
                    return ptr::null_mut();
                }
                self.data_ptr.as_ptr().add(offset)
            }
            /// ## Safety:
            /// - The caller must make sure that `offset` must be less than the capacity of the arena and larger than 0.
            #[inline]
            pub(super) unsafe fn tower<'a>(&self, offset: usize, height: usize) -> &'a Link {
                let ptr = self.get_pointer(offset + height * mem::size_of::<Link>());
                &*ptr.cast()
            }
            #[inline]
            fn inner(&self) -> &Shared {
                unsafe { &*(self.inner.load(Ordering::Acquire) as *const Shared) }
            }
            #[allow(clippy::mut_from_ref)]
            #[inline]
            fn inner_mut(&self) -> &mut Shared {
                unsafe { &mut *(self.inner.load(Ordering::Acquire) as *mut Shared) }
            }
        }
        impl Drop for Arena {
            fn drop(&mut self) {
                unsafe {
                    self.inner.with_mut(|shared| {
                        let shared: *mut Shared = shared.cast();
                        if (*shared).refs.fetch_sub(1, Ordering::Release) != 1 {
                            return;
                        }
                        (*shared).refs.load(Ordering::Acquire);
                        let mut shared = Box::from_raw(shared);
                        shared.unmount(self.n.load(Ordering::Relaxed) as usize);
                    });
                }
            }
        }
    }
    use arena::Arena;
    mod node {
        use core::ptr;
        use crate::{
            sync::{AtomicU32, Ordering},
            Key, Value,
        };
        use super::{MAX_HEIGHT, arena::Arena};
        pub(super) struct Link {
            next_offset: AtomicU32,
            prev_offset: AtomicU32,
        }
        impl Link {
            #[inline]
            pub(super) const fn new(next_offset: u32, prev_offset: u32) -> Self {
                Self {
                    next_offset: AtomicU32::new(next_offset),
                    prev_offset: AtomicU32::new(prev_offset),
                }
            }
        }
        pub(super) struct NodePtr<K: Key, V: Value> {
            pub(super) ptr: *const Node<K, V>,
            pub(super) offset: u32,
        }
        impl<K: Key, V: Value> Clone for NodePtr<K, V> {
            fn clone(&self) -> Self {
                *self
            }
        }
        impl<K: Key, V: Value> Copy for NodePtr<K, V> {}
        impl<K: Key, V: Value> NodePtr<K, V> {
            pub(super) const NULL: Self = Self {
                ptr: ptr::null(),
                offset: 0,
            };
            #[inline]
            pub(super) const fn new(ptr: *const u8, offset: u32) -> Self {
                Self {
                    ptr: ptr.cast(),
                    offset,
                }
            }
        }
        #[repr(C)]
        pub(super) struct Node<K: Key, V: Value> {
            pub(super) key_trailer: K::Trailer,
            pub(super) value_trailer: V::Trailer,
            pub(super) key_offset: u32,
            pub(super) key_size: u32,
            pub(super) value_size: u32,
            pub(super) alloc_size: u32,
        }
        #[automatically_derived]
        impl<K: ::core::fmt::Debug + Key, V: ::core::fmt::Debug + Value> ::core::fmt::Debug for Node<K, V>
        where
            K::Trailer: ::core::fmt::Debug,
            V::Trailer: ::core::fmt::Debug,
        {
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                let names: &'static _ = &[
                    "key_trailer",
                    "value_trailer",
                    "key_offset",
                    "key_size",
                    "value_size",
                    "alloc_size",
                ];
                let values: &[&dyn ::core::fmt::Debug] = &[
                    &self.key_trailer,
                    &self.value_trailer,
                    &self.key_offset,
                    &self.key_size,
                    &self.value_size,
                    &&self.alloc_size,
                ];
                ::core::fmt::Formatter::debug_struct_fields_finish(f, "Node", names, values)
            }
        }
        impl<K: Key, V: Value> Node<K, V> {
            pub(super) const ALIGNMENT: usize = core::mem::align_of::<Self>() - 1;
            pub(super) const SIZE: usize = core::mem::size_of::<Self>();
            pub(super) const MAX_NODE_SIZE: u64 =
                (Self::SIZE + MAX_HEIGHT * core::mem::size_of::<Link>()) as u64;
            /// Returns the maximum space needed for a node with the specified
            /// key and value sizes. This could overflow a `u32`, which is why a uint64
            /// is used here. If a key/value overflows a `u32`, it should not be added to
            /// the skiplist.
            pub(super) const fn max_node_size(key_size: u32, value_size: u32) -> u64 {
                Self::MAX_NODE_SIZE + key_size as u64 + value_size as u64 + Self::ALIGNMENT as u64
            }
        }
        impl<K: Key, V: Value> Node<K, V> {
            /// ## Safety
            ///
            /// - The caller must ensure that the node is allocated by the arena.
            pub(super) unsafe fn get_key<'a, 'b: 'a>(&'a self, arena: &'b Arena) -> &'b [u8] {
                arena.get_bytes(self.key_offset as usize, self.key_size as usize)
            }
            /// ## Safety
            ///
            /// - The caller must ensure that the node is allocated by the arena.
            pub(super) unsafe fn get_value<'a, 'b: 'a>(&'a self, arena: &'b Arena) -> &'b [u8] {
                arena.get_bytes(
                    self.key_offset as usize + self.key_size as usize,
                    self.value_size as usize,
                )
            }
            /// ## Safety
            ///
            /// - The caller must ensure that the node is allocated by the arena.
            /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
            pub(super) unsafe fn next_offset(&self, arena: &Arena, offset: u32, h: usize) -> u32 {
                arena
                    .tower(offset as usize, h)
                    .next_offset
                    .load(Ordering::Acquire)
            }
            /// ## Safety
            ///
            /// - The caller must ensure that the node is allocated by the arena.
            /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
            pub(super) unsafe fn prev_offset(&self, arena: &Arena, offset: u32, h: usize) -> u32 {
                arena
                    .tower(offset as usize, h)
                    .prev_offset
                    .load(Ordering::Acquire)
            }
        }
    }
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
    pub struct SkipMap<K, V, C: Comparator = ()> {
        arena: Arena,
        head_offset: u32,
        tail_offset: u32,
        /// Current height. 1 <= height <= kMaxHeight. CAS.
        height: CachePadded<AtomicU32>,
        cmp: C,
        _k: core::marker::PhantomData<K>,
        _v: core::marker::PhantomData<V>,
    }
    #[automatically_derived]
    impl<K: ::core::fmt::Debug, V: ::core::fmt::Debug, C: ::core::fmt::Debug + Comparator>
        ::core::fmt::Debug for SkipMap<K, V, C>
    {
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            let names: &'static _ = &[
                "arena",
                "head_offset",
                "tail_offset",
                "height",
                "cmp",
                "_k",
                "_v",
            ];
            let values: &[&dyn ::core::fmt::Debug] = &[
                &self.arena,
                &self.head_offset,
                &self.tail_offset,
                &self.height,
                &self.cmp,
                &self._k,
                &&self._v,
            ];
            ::core::fmt::Formatter::debug_struct_fields_finish(f, "SkipMap", names, values)
        }
    }
    impl<K, V, C: Comparator> SkipMap<K, V, C> {
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
    impl<K: Key, V: Value, C: Comparator> SkipMap<K, V, C> {
        /// Returns true if the key exists in the map.
        #[inline]
        pub fn contains_key<'a, Q>(&self, key: &Q) -> bool
        where
            KeyRef<'a, K>: core::borrow::Borrow<Q>,
            K::Trailer: 'a,
            Q: Ord + ?Sized,
        {
            self.get(key).is_some()
        }
        /// Returns the value associated with the given key, if it exists.
        pub fn get<'a, Q>(&self, key: &Q) -> Option<&[u8]>
        where
            KeyRef<'a, K>: core::borrow::Borrow<Q>,
            K::Trailer: 'a,
            Q: Ord + ?Sized,
        {
            ::core::panicking::panic("not yet implemented")
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
        pub fn get_or_insert<'a, Q>(&self, key: &Q, value: &[u8]) -> Result<&[u8], Error>
        where
            KeyRef<'a, K>: core::borrow::Borrow<Q>,
            K::Trailer: 'a,
            Q: Ord + ?Sized,
        {
            ::core::panicking::panic("not yet implemented")
        }
        /// Inserts a new key if it does not yet exist. Returns `Ok(())` if the key was successfully inserted.
        ///
        /// As a low-level crate, users are expected to handle the error cases themselves.
        ///
        /// # Errors
        ///
        /// - Returns `Error::Duplicated`, if the key already exists.
        /// - Returns `Error::Full`, if there isn't enough room in the arena.
        pub fn insert<'a, Q>(&self, key: &Q, value: &[u8]) -> Result<(), Error>
        where
            KeyRef<'a, K>: core::borrow::Borrow<Q>,
            K::Trailer: 'a,
            Q: Ord + ?Sized,
        {
            ::core::panicking::panic("not yet implemented")
        }
    }
    impl<K: Key, V: Value, C: Comparator> SkipMap<K, V, C> {
        unsafe fn find_splice(&self, key: KeyRef<K>) -> bool {
            let list_height = self.height();
            ::core::panicking::panic("not yet implemented")
        }
        /// ## Safety
        /// - `level` is less than `MAX_HEIGHT`.
        /// - `start` must be allocated by self's arena.
        unsafe fn find_splice_for_level(
            &self,
            key: KeyRef<K>,
            level: usize,
            start: NodePtr<K, V>,
        ) -> Splice<K, V> {
            let mut prev = start;
            loop {
                let next = self.get_next(prev, level);
                if next.offset == self.tail_offset {
                    return Splice {
                        prev,
                        next,
                        found: false,
                    };
                }
                let next_node = &*next.ptr;
                let (key_offset, key_size) = (next_node.key_offset, next_node.key_size);
                let next_key = self.arena.get_bytes(key_offset as usize, key_size as usize);
                match self.cmp.compare(key.as_bytes(), next_key) {
                    cmp::Ordering::Less => {
                        return Splice {
                            prev,
                            next,
                            found: false,
                        }
                    }
                    cmp::Ordering::Greater => prev = next,
                    cmp::Ordering::Equal => {
                        let trailer = key.trailer();
                        if next_node.key_trailer.eq(trailer) {
                            return Splice {
                                prev,
                                next,
                                found: true,
                            };
                        }
                        if trailer.gt(&next_node.key_trailer) {
                            return Splice {
                                prev,
                                next,
                                found: false,
                            };
                        }
                    }
                }
            }
        }
        /// ## Safety
        /// - The caller must ensure that the node is allocated by the arena.
        unsafe fn key_is_after_node(&self, nd: &Node<K, V>, key: KeyRef<K>) -> bool {
            let nd_key = self
                .arena
                .get_bytes(nd.key_offset as usize, nd.key_size as usize);
            match self.cmp.compare(nd_key, key.as_bytes()) {
                cmp::Ordering::Less => true,
                cmp::Ordering::Greater => false,
                cmp::Ordering::Equal => {
                    let key_trailer = key.trailer();
                    if nd.key_trailer.eq(key_trailer) {
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
            nd: *const Node<K, V>,
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
        unsafe fn get_next(&self, nptr: NodePtr<K, V>, height: usize) -> NodePtr<K, V> {
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
    struct Splice<K: Key, V: Value> {
        prev: NodePtr<K, V>,
        next: NodePtr<K, V>,
        found: bool,
    }
}
const NODE_ALIGNMENT_FACTOR: usize = core::mem::align_of::<u32>();
/// Comparator is used for users to define their own key comparison logic.
/// e.g. some key-value database developers may want to alpabetically comparation
pub trait Comparator {
    /// Compares two byte slices.
    fn compare(&self, a: &[u8], b: &[u8]) -> core::cmp::Ordering;
}
impl Comparator for () {
    #[inline]
    fn compare(&self, a: &[u8], b: &[u8]) -> core::cmp::Ordering {
        a.cmp(b)
    }
}
/// Gives the key-value database developers the ability to add extra information
/// to the key or value provided by the end-users.
///
/// **NB:**
///
/// The alignment of the type implements this trait must be a multiple of `4`,
/// typically a `u32`, `u64`, `u128` and etc.
/// This is forced to guarantee we must make sure there is no read unalignment pointer happen,
/// since read unalignment pointer will lead to UB(Undefined Behavior) on some platforms.
///
/// See [`Key`](crate::Key) and [`Value`](crate::Value) for more details.
pub trait Trailer: Sized + Ord {}
impl Trailer for () {}
/// Re-export bytes crate
pub use bytes;
mod sync {
    #[cfg(not(loom))]
    pub(crate) use core::sync::atomic::*;
    #[cfg(not(loom))]
    pub(crate) trait AtomicMut<T> {
        fn with_mut<F, R>(&mut self, f: F) -> R
        where
            F: FnOnce(&mut *mut T) -> R;
    }
    #[cfg(not(loom))]
    impl<T> AtomicMut<T> for AtomicPtr<T> {
        fn with_mut<F, R>(&mut self, f: F) -> R
        where
            F: FnOnce(&mut *mut T) -> R,
        {
            f(self.get_mut())
        }
    }
}
