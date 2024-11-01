use core::mem;

pub use rarena_allocator::Freelist;
use rarena_allocator::Options as ArenaOptions;

use super::{
  allocator::{Node, Sealed as AllocatorSealed},
  Height, KeySize,
};

use crate::{allocator::Sealed, Arena, Error};

/// The memory format version.
pub(crate) const CURRENT_VERSION: u16 = 0;

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
mod open_options;

/// Configuration for the compression policy of the key in [`Arena`](crate::traits::Arena).
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum CompressionPolicy {
  /// Fast compression policy, which only checks if the key is a prefix of the next key.
  #[default]
  Fast,
  /// High compression policy, which checks if the key is a substring of the next key.
  #[cfg(feature = "experimental")]
  #[cfg_attr(docsrs, doc(cfg(feature = "experimental")))]
  High,
}

/// Options for [`Arena`](crate::traits::Arena).
#[viewit::viewit(vis_all = "pub(super)", getters(skip), setters(skip))]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Options {
  max_value_size: u32,
  max_key_size: KeySize,
  max_height: Height,
  magic_version: u16,
  capacity: Option<u32>,
  unify: bool,
  freelist: Freelist,
  policy: CompressionPolicy,
  reserved: u32,
  lock_meta: bool,

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  create_new: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  create: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  read: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  write: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  append: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  truncate: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  offset: u64,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  stack: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  huge: Option<u8>,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  populate: bool,
}

impl Default for Options {
  #[inline]
  fn default() -> Options {
    Options::new()
  }
}

impl Options {
  /// Creates a new set of options with the default values.
  #[inline]
  pub const fn new() -> Self {
    Self {
      max_value_size: u32::MAX,
      max_key_size: KeySize::MAX,
      max_height: Height::new(),
      capacity: None,
      unify: false,
      magic_version: 0,
      freelist: Freelist::None,
      policy: CompressionPolicy::Fast,
      reserved: 0,
      lock_meta: true,

      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      create_new: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      create: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      read: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      write: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      append: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      truncate: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      offset: 0,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      stack: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      huge: None,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      populate: false,
    }
  }

  /// Set the reserved bytes of the ARENA.
  ///
  /// The reserved is used to configure the start position of the ARENA. This is useful
  /// when you want to add some bytes before the ARENA, e.g. when using the memory map file backed ARENA,
  /// you can set the reserved to the size to `8` to store a 8 bytes checksum.
  ///
  /// The default reserved is `0`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_reserved(8);
  /// ```
  #[inline]
  pub const fn with_reserved(mut self, reserved: u32) -> Self {
    self.reserved = reserved;
    self
  }

  /// Set if lock the meta of the ARENA in the memory to prevent OS from swapping out the first page of ARENA.
  /// When using memory map backed ARENA, the meta of the ARENA
  /// is in the first page, meta is frequently accessed,
  /// lock (`mlock` on the first page) the meta can reduce the page fault,
  /// but yes, this means that one `SkipMap` will have one page are locked in memory,
  /// and will not be swapped out. So, this is a trade-off between performance and memory usage.
  ///
  /// Default is `true`.
  ///
  /// This configuration has no effect on windows and vec backed ARENA.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_lock_meta(false);
  /// ```
  #[inline]
  pub const fn with_lock_meta(mut self, lock_meta: bool) -> Self {
    self.lock_meta = lock_meta;
    self
  }

  /// Set the magic version of the [`Arena`](crate::traits::Arena).
  ///
  /// This is used by the application using [`Arena`](crate::traits::Arena)
  /// to ensure that it doesn't open the [`Arena`](crate::traits::Arena)
  /// with incompatible data format.
  ///  
  /// The default value is `0`.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_magic_version(1);
  /// ```
  #[inline]
  pub const fn with_magic_version(mut self, magic_version: u16) -> Self {
    self.magic_version = magic_version;
    self
  }

  /// Set the [`Freelist`] kind of the [`Arena`](crate::traits::Arena).
  ///
  /// The default value is [`Freelist::Optimistic`].
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::{Options, Freelist};
  ///
  /// let opts = Options::new().with_freelist(Freelist::Optimistic);
  /// ```
  #[inline]
  pub const fn with_freelist(mut self, freelist: Freelist) -> Self {
    self.freelist = freelist;
    self
  }

  /// Set the compression policy of the key in [`Arena`](crate::traits::Arena).
  ///
  /// The default value is [`CompressionPolicy::Fast`].
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::{Options, CompressionPolicy};
  ///
  /// let opts = Options::new().with_compression_policy(CompressionPolicy::Fast);
  /// ```
  #[inline]
  pub const fn with_compression_policy(mut self, policy: CompressionPolicy) -> Self {
    self.policy = policy;
    self
  }

  /// Set if use the unify memory layout of the [`Arena`](crate::traits::Arena).
  ///
  /// File backed [`Arena`](crate::traits::Arena) has different memory layout with other kind backed [`Arena`](crate::traits::Arena),
  /// set this value to `true` will unify the memory layout of the [`Arena`](crate::traits::Arena), which means
  /// all kinds of backed [`Arena`](crate::traits::Arena) will have the same memory layout.
  ///
  /// This value will be ignored if the [`Arena`](crate::traits::Arena) is backed by a file backed memory map.
  ///
  /// The default value is `false`.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_unify(true);
  /// ```
  #[inline]
  pub const fn with_unify(mut self, unify: bool) -> Self {
    self.unify = unify;
    self
  }

  /// Sets the maximum size of the value.
  ///
  /// Default is `u32::MAX`.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::Options;
  ///
  /// let options = Options::new().with_max_value_size(1024);
  /// ```
  #[inline]
  pub const fn with_max_value_size(mut self, size: u32) -> Self {
    self.max_value_size = size;
    self
  }

  /// Sets the maximum size of the key.
  ///
  /// The maximum size of the key is `u27::MAX`.
  ///
  /// Default is `65535`.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::{Options, KeySize};
  ///
  /// let options = Options::new().with_max_key_size(KeySize::new());
  /// ```
  #[inline]
  pub const fn with_max_key_size(mut self, size: KeySize) -> Self {
    self.max_key_size = size;
    self
  }

  /// Sets the maximum height.
  ///
  /// Default is `20`. The maximum height is `31`. The minimum height is `1`.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::{Options, Height};
  ///
  /// let options = Options::new().with_max_height(Height::new());
  /// ```
  #[inline]
  pub const fn with_max_height(mut self, height: Height) -> Self {
    self.max_height = height;
    self
  }

  /// Sets the capacity of the underlying ARENA.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::Options;
  ///
  /// let options = Options::new().with_capacity(1024);
  /// ```
  #[inline]
  pub const fn with_capacity(mut self, capacity: u32) -> Self {
    self.capacity = Some(capacity);
    self
  }

  /// Get the reserved of the ARENA.
  ///
  /// The reserved is used to configure the start position of the ARENA. This is useful
  /// when you want to add some bytes before the ARENA, e.g. when using the memory map file backed ARENA,
  /// you can set the reserved to the size to `8` to store a 8 bytes checksum.
  ///
  /// The default reserved is `0`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_reserved(8);
  ///
  /// assert_eq!(opts.reserved(), 8);
  /// ```
  #[inline]
  pub const fn reserved(&self) -> u32 {
    self.reserved
  }

  /// Get if lock the meta of the ARENA in the memory to prevent OS from swapping out the first page of ARENA.
  /// When using memory map backed ARENA, the meta of the ARENA
  /// is in the first page, meta is frequently accessed,
  /// lock (`mlock` on the first page) the meta can reduce the page fault,
  /// but yes, this means that one `SkipMap` will have one page are locked in memory,
  /// and will not be swapped out. So, this is a trade-off between performance and memory usage.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_lock_meta(false);
  ///
  /// assert_eq!(opts.lock_meta(), false);
  /// ```
  #[inline]
  pub const fn lock_meta(&self) -> bool {
    self.lock_meta
  }

  /// Returns the maximum size of the value.
  ///
  /// Default is `u32::MAX`. The maximum size of the value is `u32::MAX - header`.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::Options;
  ///
  /// let options = Options::new().with_max_value_size(1024);
  /// ```
  #[inline]
  pub const fn max_value_size(&self) -> u32 {
    self.max_value_size
  }

  /// Returns the maximum size of the key.
  ///
  /// The maximum size of the key is `u27::MAX`.
  ///
  /// Default is `65535`.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::{Options, KeySize};
  ///
  /// let options = Options::new().with_max_key_size(KeySize::new());
  ///
  /// assert_eq!(options.max_key_size(), u16::MAX);
  /// ```
  #[inline]
  pub const fn max_key_size(&self) -> KeySize {
    self.max_key_size
  }

  /// Returns the maximum height.
  ///
  /// Default is `20`. The maximum height is `31`. The minimum height is `1`.
  ///
  /// ## Example
  ///
  /// ```
  /// use skl::{Options, Height};
  ///
  /// let options = Options::new().with_max_height(Height::from_u8_unchecked(5));
  ///
  /// assert_eq!(options.max_height(), 5);
  /// ```
  #[inline]
  pub const fn max_height(&self) -> Height {
    self.max_height
  }

  /// Returns the configuration of underlying ARENA size.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let options = Options::new().with_capacity(1024);
  /// ```
  #[inline]
  pub const fn capacity(&self) -> u32 {
    match self.capacity {
      Some(capacity) => capacity,
      None => 0,
    }
  }

  /// Get if use the unify memory layout of the [`Arena`](crate::traits::Arena).
  ///
  /// File backed [`Arena`](crate::traits::Arena) has different memory layout with other kind backed [`Arena`](crate::traits::Arena),
  /// set this value to `true` will unify the memory layout of the [`Arena`](crate::traits::Arena), which means
  /// all kinds of backed [`Arena`](crate::traits::Arena) will have the same memory layout.
  ///
  /// This value will be ignored if the [`Arena`](crate::traits::Arena) is backed by a file backed memory map.
  ///  
  /// The default value is `false`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_unify(true);
  ///
  /// assert_eq!(opts.unify(), true);
  /// ```
  #[inline]
  pub const fn unify(&self) -> bool {
    self.unify
  }

  /// Get the magic version of the [`Arena`](crate::traits::Arena).
  ///
  /// This is used by the application using [`Arena`](crate::traits::Arena)
  /// to ensure that it doesn't open the [`Arena`](crate::traits::Arena)
  /// with incompatible data format.
  ///
  /// The default value is `0`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::Options;
  ///
  /// let opts = Options::new().with_magic_version(1);
  ///
  /// assert_eq!(opts.magic_version(), 1);
  /// ```
  #[inline]
  pub const fn magic_version(&self) -> u16 {
    self.magic_version
  }

  /// Get the [`Freelist`] kind of the [`Arena`](crate::traits::Arena).
  ///
  /// The default value is [`Freelist::Optimistic`].
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{Options, Freelist};
  ///
  /// let opts = Options::new().with_freelist(Freelist::Optimistic);
  ///
  /// assert_eq!(opts.freelist(), Freelist::Optimistic);
  /// ```
  #[inline]
  pub const fn freelist(&self) -> Freelist {
    self.freelist
  }

  /// Get the compression policy of the keys in [`Arena`](crate::traits::Arena).
  ///
  /// The default value is [`CompressionPolicy::Fast`].
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{Options, CompressionPolicy};
  ///
  /// let opts = Options::new().with_compression_policy(CompressionPolicy::Fast);
  ///
  /// assert_eq!(opts.compression_policy(), CompressionPolicy::Fast);
  /// ```
  #[inline]
  pub const fn compression_policy(&self) -> CompressionPolicy {
    self.policy
  }

  /// Returns the data offset of the `SkipMap` if the `SkipMap` is in unified memory layout.
  ///
  /// See also [`Options::data_offset`].
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{map::sync, multiple_version::unsync, Options, Arena};
  ///
  /// // Create a sync skipmap which supports both trailer and version.
  /// let opts = Options::new().with_capacity(1024);
  /// let data_offset_from_opts = opts.data_offset::<_, _, sync::SkipMap<[u8], [u8]>>();
  /// let map = opts.alloc::<_, _, sync::SkipMap<[u8], [u8]>>().unwrap();
  /// assert_eq!(data_offset_from_opts, map.data_offset());
  ///
  /// let data_offset_from_opts = opts.data_offset_unify::<_, _, sync::SkipMap<[u8], [u8]>>();
  /// let map = opts.with_unify(true).alloc::<_, _, sync::SkipMap<[u8], [u8]>>().unwrap();
  /// assert_eq!(data_offset_from_opts, map.data_offset());
  ///
  /// // Create a unsync ARENA.
  /// let opts = Options::new().with_capacity(1024);
  /// let data_offset_from_opts = opts.data_offset::<_, _, unsync::SkipMap<[u8], [u8]>>();
  /// let map = opts.alloc::<_, _, unsync::SkipMap<[u8], [u8]>>().unwrap();
  /// assert_eq!(data_offset_from_opts, map.data_offset());
  ///
  /// let data_offset_from_opts = opts.data_offset_unify::<_, _, unsync::SkipMap<[u8], [u8]>>();
  /// let map = opts.with_unify(true).alloc::<_, _, unsync::SkipMap<[u8], [u8]>>().unwrap();
  /// assert_eq!(data_offset_from_opts, map.data_offset());
  /// ```
  pub fn data_offset_unify<K, V, A>(&self) -> usize
  where
    K: ?Sized + 'static,
    V: ?Sized + 'static,
    A: Arena<K, V>,
  {
    let arena_opts = self.to_arena_options();
    let arena_data_offset =
      arena_opts.data_offset_unify::<<A::Allocator as AllocatorSealed>::Allocator>();

    data_offset_in::<A::Allocator>(arena_data_offset, self.max_height(), true)
  }

  /// Returns the data offset of the `SkipMap` if the `SkipMap` is not in unified memory layout.
  ///
  /// As the file backed `SkipMap` will only use the unified memory layout and ignore the unify configuration of `Options`,
  /// so see also [`Options::data_offset_unify`], if you want to get the data offset of the `SkipMap` in unified memory layout.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{map::sync, multiple_version::unsync, Options, Arena};
  ///
  /// // Create a sync skipmap which supports both trailer and version.
  /// let opts = Options::new().with_capacity(1024);
  /// let data_offset_from_opts = opts.data_offset::<_, _, sync::SkipMap<[u8], [u8]>>();
  /// let map = opts.alloc::<_, _, sync::SkipMap<[u8], [u8]>>().unwrap();
  /// assert_eq!(data_offset_from_opts, map.data_offset());
  ///
  /// let data_offset_from_opts = opts.data_offset_unify::<_, _, sync::SkipMap<[u8], [u8]>>();
  /// let map = opts.with_unify(true).alloc::<_, _, sync::SkipMap<[u8], [u8]>>().unwrap();
  /// assert_eq!(data_offset_from_opts, map.data_offset());
  ///
  /// // Create a unsync ARENA.
  /// let opts = Options::new().with_capacity(1024);
  /// let data_offset_from_opts = opts.data_offset::<_, _, unsync::SkipMap<[u8], [u8]>>();
  /// let map = opts.alloc::<_, _, unsync::SkipMap<[u8], [u8]>>().unwrap();
  /// assert_eq!(data_offset_from_opts, map.data_offset());
  ///
  /// let data_offset_from_opts = opts.data_offset_unify::<_, _, unsync::SkipMap<[u8], [u8]>>();
  /// let map = opts.with_unify(true).alloc::<_, _, unsync::SkipMap<[u8], [u8]>>().unwrap();
  /// assert_eq!(data_offset_from_opts, map.data_offset());
  /// ```
  pub fn data_offset<K, V, A>(&self) -> usize
  where
    K: ?Sized + 'static,
    V: ?Sized + 'static,
    A: Arena<K, V>,
  {
    let arena_opts = self.to_arena_options();
    let arena_data_offset =
      arena_opts.data_offset::<<A::Allocator as crate::allocator::Sealed>::Allocator>();
    data_offset_in::<A::Allocator>(arena_data_offset, self.max_height(), false)
  }
}

impl Options {
  #[allow(clippy::wrong_self_convention)]
  #[inline]
  pub(super) const fn to_arena_options(&self) -> ArenaOptions {
    let opts = ArenaOptions::new()
      .with_magic_version(CURRENT_VERSION)
      .with_reserved(self.reserved())
      .with_unify(self.unify())
      .maybe_capacity(self.capacity)
      .with_freelist(self.freelist());

    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    {
      opts
        .with_lock_meta(false) // we need to avoid arena's lock_meta
        .with_create(self.create())
        .with_create_new(self.create_new())
        .with_read(self.read())
        .with_write(self.write())
        .with_append(self.append())
        .with_truncate(self.truncate())
        .with_offset(self.offset())
        .with_stack(self.stack())
        .with_huge(self.huge())
        .with_populate(self.populate())
    }

    #[cfg(not(all(feature = "memmap", not(target_family = "wasm"))))]
    opts
  }
}

impl Options {
  /// Create a new map which is backed by a `AlignedVec`.
  ///
  /// **Note:** The capacity stands for how many memory allocated,
  /// it does not mean the skiplist can store `cap` entries.
  ///
  /// **What the difference between this method and [`Options::map_anon`]?**
  ///
  /// 1. This method will use an `AlignedVec` ensures we are working within Rust's memory safety guarantees.
  ///    Even if we are working with raw pointers with `Box::into_raw`,
  ///    the backend ARENA will reclaim the ownership of this memory by converting it back to a `Box`
  ///    when dropping the backend ARENA. Since `AlignedVec` uses heap memory, the data might be more cache-friendly,
  ///    especially if you're frequently accessing or modifying it.
  ///
  /// 2. Where as [`Options::map_anon`] will use mmap anonymous to require memory from the OS.
  ///    If you require very large contiguous memory regions, `mmap` might be more suitable because
  ///    it's more direct in requesting large chunks of memory from the OS.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use skl::{map::sync, multiple_version::unsync, Options};
  ///
  /// // Create a sync skipmap which supports both trailer and version.
  /// let map = Options::new().with_capacity(1024).alloc::<_, _, sync::SkipMap<[u8], [u8]>>().unwrap();
  ///
  /// // Create a unsync skipmap which supports trailer.
  /// let arena = Options::new().with_capacity(1024).alloc::<_, _, unsync::SkipMap<[u8], [u8]>>().unwrap();
  /// ```
  #[inline]
  pub fn alloc<K, V, T>(self) -> Result<T, Error>
  where
    K: ?Sized + 'static,
    V: ?Sized + 'static,
    T: Arena<K, V>,
  {
    let node_align = mem::align_of::<<T::Allocator as Sealed>::Node>();

    self
      .to_arena_options()
      .with_maximum_alignment(node_align)
      .alloc::<<T::Allocator as Sealed>::Allocator>()
      .map_err(Into::into)
      .and_then(|arena| T::construct(arena, self, false))
  }
}

#[inline]
fn data_offset_in<A: AllocatorSealed>(offset: usize, max_height: Height, unify: bool) -> usize {
  let meta_end = if unify {
    let alignment = mem::align_of::<A::Header>();
    let meta_offset = (offset + alignment - 1) & !(alignment - 1);
    meta_offset + mem::size_of::<A::Header>()
  } else {
    offset
  };

  let alignment = mem::align_of::<A::Node>();
  let head_offset = (meta_end + alignment - 1) & !(alignment - 1);
  let head_end = head_offset
    + mem::size_of::<A::Node>()
    + mem::size_of::<<A::Node as Node>::Link>() * max_height.to_usize();

  let tail_offset = (head_end + alignment - 1) & !(alignment - 1);
  tail_offset
    + mem::size_of::<A::Node>()
    + mem::size_of::<<A::Node as Node>::Link>() * max_height.to_usize()
}
