use core::ptr::NonNull;

use super::{
  Arena, GenericAllocator, Link, Node, Ordering, UnsyncValuePointer, ValuePointer, Version,
  VersionedMeta, WithVersion,
};
use crate::{internal::Flags, MIN_VERSION};

pub(crate) type Allocator = GenericAllocator<VersionedMeta, VersionedNode, Arena>;

node!(
  /// A node that only supports version.
  struct VersionedNode {
    flags = Flags::MULTIPLE_VERSION;
    version: u64 = MIN_VERSION;

    {
      type Link = Link;

      type ValuePointer = UnsyncValuePointer;
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
