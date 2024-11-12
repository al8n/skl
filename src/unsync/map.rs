use super::*;

node!(
  /// A raw node that does not support version.
  struct RawNode {
    flags = Flags::empty();

    {
      type Link = Link;

      type ValuePointer = UnsyncValuePointer;
      type Pointer = NodePointer<T>;

      fn set_version(&mut self, version: Version) {}

      impl WithoutVersion for RawNode {}

      node_pointer!(RawNode {{
        fn version(&self) -> Version {
          MIN_VERSION
        }
      }});
    }
  }
);

/// The allocator used to allocate nodes in the `SkipMap`.
pub type Allocator = GenericAllocator<Meta, RawNode, Arena>;
