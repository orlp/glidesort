use core::mem::MaybeUninit;

use crate::mut_slice::states::{AlwaysInit, Uninit};
use crate::mut_slice::{Brand, MutSlice};
use crate::physical_merges::{physical_merge, physical_quad_merge, physical_triple_merge};
use crate::stable_quicksort::quicksort;
#[cfg(feature = "tracking")]
use crate::tracking::ptr;
use crate::util::*;
use crate::{powersort, small_sort, tracking, SMALL_SORT};

/// A logical run of elements, which can be a series of unsorted elements,
/// a sorted run, or two sorted runs adjacent in memory.
pub enum LogicalRun<'l, B: Brand, T> {
    Unsorted(MutSlice<'l, B, T, AlwaysInit>),
    Sorted(MutSlice<'l, B, T, AlwaysInit>),
    DoubleSorted(MutSlice<'l, B, T, AlwaysInit>, usize),
}

impl<'l, B: Brand, T> LogicalRun<'l, B, T> {
    /// The length of this logical run.
    fn len(&self) -> usize {
        match self {
            LogicalRun::Unsorted(r) => r.len(),
            LogicalRun::Sorted(r) => r.len(),
            LogicalRun::DoubleSorted(r, _mid) => r.len(),
        }
    }

    /// Create a new logical run at the start of el, returning the rest.
    fn create<F: Cmp<T>>(
        mut el: MutSlice<'l, B, T, AlwaysInit>,
        is_less: &mut F,
        eager_smallsort: bool,
    ) -> (Self, MutSlice<'l, B, T, AlwaysInit>) {
        // Check if input is (partially) pre-sorted in a meaningful way.
        if el.len() >= SMALL_SORT {
            let (run_length, descending) = run_length_at_start(el.as_mut_slice(), is_less);
            if run_length >= SMALL_SORT {
                if descending {
                    #[cfg(feature = "tracking")]
                    {
                        for i in 0..run_length / 2 {
                            unsafe {
                                ptr::swap_nonoverlapping(
                                    el.begin().add(i),
                                    el.begin().add(run_length - 1 - i),
                                    1,
                                );
                            }
                        }
                    }
                    #[cfg(not(feature = "tracking"))]
                    {
                        el.as_mut_slice()[..run_length].reverse();
                    }
                }
                let (run, rest) = el.split_at(run_length).unwrap();
                return (LogicalRun::Sorted(run), rest);
            }
        }

        // Otherwise create a small unsorted run. Capping this at SMALL_SORT ensures
        // we're always able to sort this later, regardless of scratch space size.
        let skip = SMALL_SORT.min(el.len());
        let (mut run, rest) = el.split_at(skip).unwrap();
        if eager_smallsort {
            small_sort::small_sort(run.borrow(), is_less);
            (LogicalRun::Sorted(run), rest)
        } else {
            (LogicalRun::Unsorted(run), rest)
        }
    }

    /// Merges runs self (left) and right using the given scratch space.
    ///
    /// Panics if is_less does, aborts if left, right aren't contiguous.
    fn logical_merge<'sc, BS: Brand, F: Cmp<T>>(
        self,
        right: LogicalRun<'l, B, T>,
        mut scratch: MutSlice<'sc, BS, T, Uninit>,
        is_less: &mut F,
    ) -> LogicalRun<'l, B, T> {
        use LogicalRun::*;
        match (self, right) {
            // Only combine unsorted runs if it still fits in the scratch space.
            (Unsorted(l), Unsorted(r)) if l.len() + r.len() <= scratch.len() => {
                Unsorted(l.concat(r))
            }
            (Unsorted(l), r) => {
                let l = quicksort(l, scratch.borrow(), is_less);
                Sorted(l).logical_merge(r, scratch, is_less)
            }
            (l, Unsorted(r)) => {
                let r = quicksort(r, scratch.borrow(), is_less);
                l.logical_merge(Sorted(r), scratch, is_less)
            }
            (Sorted(l), Sorted(r)) => {
                let mid = l.len();
                DoubleSorted(l.concat(r), mid)
            }
            (DoubleSorted(l, mid), Sorted(r)) => {
                let (l0, l1) = l.split_at(mid).unwrap();
                Sorted(physical_triple_merge(l0, l1, r, scratch, is_less))
            }
            (Sorted(l), DoubleSorted(r, mid)) => {
                let (r0, r1) = r.split_at(mid).unwrap();
                Sorted(physical_triple_merge(l, r0, r1, scratch, is_less))
            }
            (DoubleSorted(l, lmid), DoubleSorted(r, rmid)) => {
                let (l0, l1) = l.split_at(lmid).unwrap();
                let (r0, r1) = r.split_at(rmid).unwrap();
                Sorted(physical_quad_merge(l0, l1, r0, r1, scratch, is_less))
            }
        }
    }

    /// Ensures that this run is physically sorted.
    fn physical_sort<'sc, BS: Brand, F: Cmp<T>>(
        self,
        scratch: MutSlice<'sc, BS, T, Uninit>,
        is_less: &mut F,
    ) -> MutSlice<'l, B, T, AlwaysInit> {
        match self {
            LogicalRun::Sorted(run) => run,
            LogicalRun::Unsorted(run) => quicksort(run, scratch, is_less),
            LogicalRun::DoubleSorted(run, mid) => {
                let (left, right) = run.split_at(mid).unwrap();
                physical_merge(left, right, scratch, is_less)
            }
        }
    }
}

// Each logical run on the merge stack represents a node in the merge tree. This
// node has fully completed merging its left children, the result of these merge
// operations is the logical run stored on the stack (even though physically the
// run might be DoubleSorted in which case it would still need one more merge
// operation).
//
// Each node doesn't know exactly its depth in the final merge tree, but it does
// know which depth it would *like* to have in the final merge tree. Using these
// desired depths calculated using Powersort's logic we decide which logical
// runs to merge if any when a new run arrives. Powersort guarantees that our
// stack size remains constant if we follow these merge depths as any desired
// depth is less than 64 and the desired depths on the stack is strictly ascending.
struct MergeStack<'l, B: Brand, T> {
    left_children: [MaybeUninit<LogicalRun<'l, B, T>>; 64],
    desired_depths: [MaybeUninit<u8>; 64],
    len: usize,
}

impl<'l, B: Brand, T> MergeStack<'l, B, T> {
    /// Creates an empty merge stack.
    fn new() -> Self {
        unsafe {
            // SAFETY: an array of MaybeUninit's is trivially init.
            Self {
                left_children: MaybeUninit::uninit().assume_init(),
                desired_depths: MaybeUninit::uninit().assume_init(),
                len: 0,
            }
        }
    }

    /// Push a merge node on the stack given its left child and desired depth.
    fn push_node(&mut self, left_child: LogicalRun<'l, B, T>, desired_depth: u8) {
        self.left_children[self.len] = MaybeUninit::new(left_child);
        self.desired_depths[self.len] = MaybeUninit::new(desired_depth);
        self.len += 1;
    }

    /// Pop a merge node off the stack, returning its left child.
    fn pop_node(&mut self) -> Option<LogicalRun<'l, B, T>> {
        if self.len == 0 {
            return None;
        }

        // SAFETY: len > 0 guarantees this is initialized by a previous push.
        self.len -= 1;
        Some(unsafe {
            self.left_children
                .get_unchecked(self.len)
                .assume_init_read()
        })
    }

    /// Returns the desired depth of the merge node at the top of the stack.
    fn peek_desired_depth(&self) -> Option<u8> {
        if self.len == 0 {
            return None;
        }

        // SAFETY: len > 0 guarantees this is initialized by a previous push.
        Some(unsafe {
            self.desired_depths
                .get_unchecked(self.len - 1)
                .assume_init()
        })
    }
}

pub fn glidesort<'el, 'sc, BE: Brand, BS: Brand, T, F: Cmp<T>>(
    mut el: MutSlice<'el, BE, T, AlwaysInit>,
    mut scratch: MutSlice<'sc, BS, T, Uninit>,
    is_less: &mut F,
    eager_smallsort: bool,
) {
    if scratch.len() < SMALL_SORT {
        // Sanity fallback, we *need* at least SMALL_SORT buffer size.
        let mut v = Vec::with_capacity(SMALL_SORT);
        let (_, new_buffer) = split_at_spare_mut(&mut v);
        return MutSlice::from_maybeuninit_mut_slice(new_buffer, |new_scratch| {
            glidesort(el, new_scratch.assume_uninit(), is_less, eager_smallsort)
        });
    }

    tracking::register_buffer("input", el.weak());
    tracking::register_buffer("scratch", scratch.weak());

    let scale_factor = powersort::merge_tree_scale_factor(el.len());
    let mut merge_stack = MergeStack::new();

    let mut prev_run_start_idx = 0;
    let mut prev_run;
    (prev_run, el) = LogicalRun::create(el, is_less, eager_smallsort);
    while el.len() > 0 {
        let next_run_start_idx = prev_run_start_idx + prev_run.len();
        let next_run;
        (next_run, el) = LogicalRun::create(el, is_less, eager_smallsort);

        let desired_depth = powersort::merge_tree_depth(
            prev_run_start_idx,
            next_run_start_idx,
            next_run_start_idx + next_run.len(),
            scale_factor,
        );

        // Create the left child of our next node and eagerly merge all nodes
        // with a deeper desired merge depth into it.
        let mut left_child = prev_run;
        while merge_stack
            .peek_desired_depth()
            .map(|top_depth| top_depth >= desired_depth)
            .unwrap_or(false)
        {
            let left_descendant = merge_stack.pop_node().unwrap();
            left_child = left_descendant.logical_merge(left_child, scratch.borrow(), is_less);
        }

        merge_stack.push_node(left_child, desired_depth);
        prev_run_start_idx = next_run_start_idx;
        prev_run = next_run;
    }

    // Collapse the stack down to a single logical run and physically sort it.
    let mut result = prev_run;
    while let Some(left_child) = merge_stack.pop_node() {
        result = left_child.logical_merge(result, scratch.borrow(), is_less);
    }
    result.physical_sort(scratch, is_less);

    tracking::deregister_buffer("input");
    tracking::deregister_buffer("scratch");
}

/// Returns the length of the run at the start of v, and if that run is
/// strictly descending.
fn run_length_at_start<T, F: Cmp<T>>(v: &[T], is_less: &mut F) -> (usize, bool) {
    let descending = v.len() >= 2 && is_less(&v[1], &v[0]);
    if descending {
        for i in 2..v.len() {
            if !is_less(&v[i], &v[i - 1]) {
                return (i, true);
            }
        }
    } else {
        for i in 2..v.len() {
            if is_less(&v[i], &v[i - 1]) {
                return (i, false);
            }
        }
    }
    (v.len(), descending)
}
