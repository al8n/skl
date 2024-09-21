/// A trait which can be constructed from a [`Builder`](super::Builder) and some options.
pub trait Map: sealed::Sealed {}

impl<T> Map for T where T: sealed::Sealed {}

pub(crate) use sealed::AsBase;

mod sealed {
  use core::{ptr::NonNull, sync::atomic::Ordering};
  use rarena_allocator::Allocator as ArenaAllocator;

  use super::super::{
    allocator::{Allocator, AllocatorExt, Header, Link, NodePointer, Sealed as AllocatorSealed},
    base::SkipList,
    Error, Options,
  };

  pub trait AsBase {
    /// The allocator type used by the target.
    type Allocator: Allocator;
    /// The comparator type used by the target.
    type Comparator;

    fn as_base(&self) -> &SkipList<Self::Allocator, Self::Comparator>;
  }

  impl<T> Sealed for T
  where
    T: AsBase + From<SkipList<T::Allocator, T::Comparator>>,
  {
    type Allocator = T::Allocator;

    type Comparator = T::Comparator;

    fn allocator(&self) -> &Self::Allocator {
      &self.as_base().arena
    }

    #[inline]
    fn magic_version(&self) -> u16 {
      self.as_base().arena.options().magic_version()
    }

    #[inline]
    fn version(&self) -> u16 {
      ArenaAllocator::magic_version(core::ops::Deref::deref(&self.as_base().arena))
    }
  }

  /// A trait which can be constructed from a [`Builder`](super::Builder) and some options.
  pub trait Sealed: Sized + From<SkipList<Self::Allocator, Self::Comparator>> {
    /// The allocator type used by the target.
    type Allocator: Allocator;
    /// The comparator type used by the target.
    type Comparator;

    fn allocator(&self) -> &Self::Allocator;

    fn magic_version(&self) -> u16;

    fn version(&self) -> u16;

    fn construct(
      arena: <Self::Allocator as AllocatorSealed>::Allocator,
      opts: Options,
      cmp: Self::Comparator,
    ) -> Result<Self, Error> {
      use std::boxed::Box;

      let arena = <Self::Allocator as AllocatorSealed>::new(arena, opts);

      let opts = arena.options();
      let max_height: u8 = opts.max_height().into();
      let data_offset = arena.check_capacity(max_height)?;
      if arena.read_only() {
        let (meta, head, tail) = arena.get_pointers();

        return Ok(Self::from(SkipList::construct(
          arena,
          meta,
          head,
          tail,
          data_offset,
          cmp,
        )));
      }

      let meta = if opts.unify() {
        arena.allocate_header(opts.magic_version())?
      } else {
        unsafe {
          NonNull::new_unchecked(Box::into_raw(Box::new(
            <<Self::Allocator as AllocatorSealed>::Header as Header>::new(opts.magic_version()),
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

      Ok(Self::from(SkipList::construct(
        arena,
        meta,
        head,
        tail,
        data_offset,
        cmp,
      )))
    }
  }
}
