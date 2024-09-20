use core::{ptr::NonNull, sync::atomic::Ordering};
use dbutils::Comparator;
use rarena_allocator::Allocator as _;

use super::{
  allocator::{Allocator, AllocatorExt, Header, Link, Node, NodePointer, Sealed},
  Error, Options,
};

/// A trait which can be constructed from a [`Builder`](super::Builder) and some options.
pub trait Constructable: Sized {
  /// The allocator type used by the target.
  type Allocator: Allocator;
  /// The comparator type used by the target.
  type Comparator: Comparator;

  fn construct(
    arena: Self::Allocator,
    meta: NonNull<<Self::Allocator as Sealed>::Header>,
    head: <<Self::Allocator as Sealed>::Node as Node>::Pointer,
    tail: <<Self::Allocator as Sealed>::Node as Node>::Pointer,
    data_offset: u32,
    cmp: Self::Comparator,
  ) -> Self;

  fn allocator(&self) -> &Self::Allocator;

  fn new_in(
    arena: <Self::Allocator as Sealed>::Allocator,
    opts: Options,
    cmp: Self::Comparator,
  ) -> Result<Self, Error> {
    use std::boxed::Box;

    let arena = <Self::Allocator as Sealed>::new(arena, opts);

    let opts = arena.options();
    let max_height: u8 = opts.max_height().into();
    let data_offset = arena.check_capacity(max_height)?;
    if arena.read_only() {
      let (meta, head, tail) = arena.get_pointers();

      return Ok(Self::construct(arena, meta, head, tail, data_offset, cmp));
    }

    let meta = if opts.unify() {
      arena.allocate_header(opts.magic_version())?
    } else {
      unsafe {
        NonNull::new_unchecked(Box::into_raw(Box::new(
          <<Self::Allocator as Sealed>::Header as Header>::new(opts.magic_version()),
        )))
      }
    };

    let head = arena.allocate_full_node(max_height)?;
    let tail = arena.allocate_full_node(max_height)?;

    // Safety:
    // We will always allocate enough space for the head node and the tail node.
    unsafe {
      // Link all head/tail levels together.
      for i in 0..(max_height as usize) {
        let head_link = head.tower(&arena, i);
        let tail_link = tail.tower(&arena, i);
        head_link.store_next_offset(tail.offset(), Ordering::Relaxed);
        tail_link.store_prev_offset(head.offset(), Ordering::Relaxed);
      }
    }

    Ok(Self::construct(arena, meta, head, tail, data_offset, cmp))
  }
}

impl<A, C> Constructable for super::base::SkipList<A, C>
where
  A: Allocator,
  C: Comparator,
{
  type Allocator = A;
  type Comparator = C;

  fn construct(
    arena: Self::Allocator,
    meta: NonNull<<Self::Allocator as Sealed>::Header>,
    head: <<Self::Allocator as Sealed>::Node as Node>::Pointer,
    tail: <<Self::Allocator as Sealed>::Node as Node>::Pointer,
    data_offset: u32,
    cmp: Self::Comparator,
  ) -> Self {
    super::base::SkipList::construct(arena, meta, head, tail, data_offset, cmp)
  }

  fn allocator(&self) -> &Self::Allocator {
    &self.arena
  }
}
