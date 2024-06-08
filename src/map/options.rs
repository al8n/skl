const U27_MAX: u32 = (1 << 27) - 1;

/// Options for `SkipMap`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Options {
  max_value_size: u32,
  max_key_size: u32,
  max_height: u8,
  capacity: u32,
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
  pub const fn new() -> Options {
    Options {
      max_value_size: u32::MAX,
      max_key_size: U27_MAX,
      max_height: 20,
      capacity: 1024,
    }
  }

  /// Sets the maximum size of the value.
  /// 
  /// Default is `u32::MAX`.
  /// 
  /// # Example
  /// 
  /// ```
  /// use skl::map::Options;
  /// 
  /// let options = Options::new().with_max_value_size(1024);
  /// ```
  #[inline]
  pub const fn with_max_value_size(mut self, size: u32) -> Options {
    self.max_value_size = size;
    self
  }

  /// Sets the maximum size of the key.
  /// 
  /// The maximum size of the key is `u27::MAX`.
  /// 
  /// Default is `u27::MAX`.
  /// 
  /// # Example
  /// 
  /// ```
  /// use skl::map::Options;
  /// 
  /// let options = Options::new().with_max_key_size(1024);
  /// ```
  #[inline]
  pub const fn with_max_key_size(mut self, size: u32) -> Options {
    self.max_key_size = if size > U27_MAX {
      U27_MAX
    } else {
      size
    };
    self
  }

  /// Sets the maximum height.
  /// 
  /// Default is `20`. The maximum height is `32`. The minimum height is `1`.
  /// 
  /// # Example
  /// 
  /// ```
  /// use skl::map::Options;
  /// 
  /// let options = Options::new().with_max_height(20);
  /// ```
  #[inline]
  pub const fn with_max_height(mut self, height: u8) -> Options {
    self.max_height = if height == 0 {
      1
    } else if height > 32 {
      32
    } else {
      height
    };
    self
  }

  /// Sets the capacity of the underlying ARENA.
  /// 
  /// Default is `1024`. This configuration will be ignored if the map is memory-mapped.
  /// 
  /// # Example
  /// 
  /// ```
  /// use skl::map::Options;
  /// 
  /// let options = Options::new().with_capacity(1024);
  /// ```
  #[inline]
  pub const fn with_capacity(mut self, capacity: u32) -> Options {
    self.capacity = capacity;
    self
  }

  /// Returns the maximum size of the value.
  /// 
  /// Default is `u32::MAX`.
  /// 
  /// # Example
  /// 
  /// ```
  /// use skl::map::Options;
  /// 
  /// let options = Options::new().with_max_value_size(1024);
  /// ```
  #[inline]
  pub const fn max_value_size(&self) -> u32 {
    self.max_value_size
  }

  /// Returns the maximum size of the key.
  #[inline]
  pub const fn max_key_size(&self) -> u32 {
    self.max_key_size
  }

  /// Returns the maximum height.
  /// 
  /// Default is `20`. The maximum height is `32`. The minimum height is `1`.
  /// 
  /// # Example
  /// 
  /// ```
  /// use skl::map::Options;
  /// 
  /// let options = Options::new().with_max_height(20);
  /// 
  /// assert_eq!(options.max_height(), 20);
  /// ```
  #[inline]
  pub const fn max_height(&self) -> u8 {
    self.max_height
  }

  /// Returns the configuration of underlying ARENA size.
  /// 
  /// Default is `1024`. This configuration will be ignored if the map is memory-mapped.
  /// 
  /// # Example
  /// 
  /// ```rust
  /// use skl::map::Options;
  /// 
  /// let options = Options::new().with_capacity(1024);
  /// ```
  #[inline]
  pub const fn capacity(&self) -> u32 {
    self.capacity
  }
}

