use super::*;

node!(
  /// A node that supports version.
  struct VersionedNode {
    flags = Flags::MULTIPLE_VERSION;
    version: u64 = MIN_VERSION;

    {
      type Link = Link;

      type ValuePointer = AtomicValuePointer;
      type Pointer = NodePointer;

      fn set_version(&mut self, version: Version) {
        self.version = version;
      }

      impl WithVersion for VersionedNode {}

      node_pointer!(VersionedNode {
        version = MIN_VERSION;

        {
          fn version(&self) -> Version {
            { self.version }
          }
        }
      });
    }
  }
);

/// Concurrent safe allocator for multiple versioned nodes.
pub type Allocator = GenericAllocator<VersionedMeta, VersionedNode, Arena>;
