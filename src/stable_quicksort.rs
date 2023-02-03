/*
    Bidirectional partitioning.

    We assume we always have a contiguous scratch space equal in size to our
    total amount of elements in each recursive call. Similarly we assume we have
    a destination space of equal size. Our input logically consists of a single
    slice of elements, although physically it can consist of two slices. We will
    call the first slice left, and the second slice right.

    Our input slices can overlap with either scratch or destination, but the
    left slice if it overlaps must start at the beginning, and the right slice
    must end at the end of the overlap.

    In this scenario (which is the usual starting scenario) both left and right
    overlap the destination (address space goes from left-to-right, vertically
    aligned arrays overlap):

                                    [         scratch           ]
        [       destination         ]
        [    left    ][    right    ]

    We start scanning through our logical input slice from both ends: forwards
    from the start, backwards from the end. Initially that means left becomes
    forward and right becomes backward, but if either left or right is fully
    consumed the remaining slice will be split up equally into a new forwards
    and backwards pair of slices.

    In the forward scan we will put elements that are less than the pivot in the
    destination, and those that are greater than or equal in the scratch, both
    at the start. In the backwards scan we do the exact opposite and put
    elements that are less than the pivot in the scratch and those that are
    greater or equal in the destination, both at the end. Note that this also
    means the aforementioned overlaps are fine, as we will read each element
    before it gets overwritten.

    The above example might look like this after partitioning:

                                    [ >= |   scratch    |   <   ]
                                    [ c' |   d'  |  a'  |   b'  ]
        [  <    |     dst     | >=  ]
        [   a   |   b   |  c  |  d  ]

    We have marked some regions with letters. It is intended regardless of ASCII
    art accuracy, that a is as large as a', etc. Note that

        |a| + |b'| + |c'| + |d| = |a| + |b| + |c| + |d| = n,

    where n is the total number of elements. a and c' were produced by the
    forward scan, b' and d were produced by the backwards scan. Then if

        partition(left, right, dest, scratch)

    is our type signature, our two recursive calls are:

        partition(a, b', concat(a, b), concat(a', b'))
        partition(c', d, concat(c, d), concat(c', d'))

    Note that this maintains the invariant that both destination and scratch
    space equal left, right in total size. Note that it also places all elements
    smaller than the pivot before those greater or equal. When our recursive
    call total size becomes too small we simply copy left, right into the
    destination and use a dedicated small sorting routine.
*/

use core::mem::ManuallyDrop;

use crate::gap_guard::GapGuard;
use crate::mut_slice::states::{AlwaysInit, Init, Uninit, Weak};
use crate::mut_slice::{Brand, MutSlice, Unbranded};
use crate::pivot_selection::select_pivot;
use crate::small_sort;
use crate::tracking;
use crate::tracking::ptr;
use crate::util::*;

struct BidirPartitionState<'l, BD: Brand, BS: Brand, T> {
    // The elements that still have to be scanned.
    forward_scan: MutSlice<'l, Unbranded, T, Init>,
    backward_scan: MutSlice<'l, Unbranded, T, Init>,

    // Our destination and scratch output slices.
    dest: MutSlice<'l, BD, T, Weak>,
    scratch: MutSlice<'l, BS, T, Weak>,

    // To get the most optimal loop body we use this weird representation where
    // dest.begin().add(num_at_dest_begin) is our dest write head and
    // scratch_forwards_cursor.sub(num_at_dest_begin) is our scratch write head.
    // This allows us to unconditionally increment scratch_forwards_cursor each
    // iteration, instead of subtracting the negation of our conditional.
    num_at_dest_begin: usize,
    scratch_forwards_cursor: *mut T,

    // Similarly, dest_backwards_cursor.add(num_at_scratch_end).sub(1) and
    // scratch.end().sub(num_at_scratch_end + 1) are our dest write tail and
    // scratch write tail respectively.
    // Yes, this extra subtraction in the loop is faster than pre-decrementing
    // once, likely due to LLVM loop bounds proving.
    num_at_scratch_end: usize,
    dest_backwards_cursor: *mut T,
}

impl<'l, BD: Brand, BS: Brand, T> BidirPartitionState<'l, BD, BS, T> {
    pub fn new<BL, BR>(
        left: MutSlice<'l, BL, T, Init>,
        right: MutSlice<'l, BR, T, Init>,
        dest: MutSlice<'l, BD, T, Weak>,
        scratch: MutSlice<'l, BS, T, Weak>,
    ) -> Self {
        Self {
            forward_scan: left.forget_brand(),
            backward_scan: right.forget_brand(),
            num_at_dest_begin: 0,
            scratch_forwards_cursor: scratch.begin(),
            num_at_scratch_end: 0,
            dest_backwards_cursor: dest.end(),
            dest,
            scratch,
        }
    }

    /// Take ownership of the output slices, in ascending order.
    pub fn take(
        &mut self,
    ) -> (
        MutSlice<'l, BD, T, Init>,
        MutSlice<'l, BS, T, Init>,
        MutSlice<'l, BS, T, Init>,
        MutSlice<'l, BD, T, Init>,
    ) {
        unsafe {
            let less_in_dest = self.dest.split_off_begin(self.num_at_dest_begin);
            let scratch_end_ptr = self.scratch_forwards_cursor.sub(self.num_at_dest_begin);
            let num_in_scratch = scratch_end_ptr.offset_from(self.scratch.begin()) as usize;
            let geq_in_scratch = self.scratch.split_off_begin(num_in_scratch);
            self.num_at_dest_begin = 0;
            self.scratch_forwards_cursor = self.scratch.begin();

            let dest_begin_ptr = self.dest_backwards_cursor.add(self.num_at_scratch_end);
            let num_in_dest = self.dest.end().offset_from(dest_begin_ptr) as usize;
            let geq_in_dest = self.dest.split_off_end(num_in_dest);
            let less_in_scratch = self.scratch.split_off_end(self.num_at_scratch_end);
            self.num_at_scratch_end = 0;
            self.dest_backwards_cursor = self.dest.end();

            (
                less_in_dest.upgrade().assume_init(),
                less_in_scratch.upgrade().assume_init(),
                geq_in_scratch.upgrade().assume_init(),
                geq_in_dest.upgrade().assume_init(),
            )
        }
    }

    /// Partitions one element using our forward scan.
    ///
    /// SAFETY: self.forward_scan may not be empty.
    #[inline]
    unsafe fn partition_one_forward<F: Cmp<T>>(
        &mut self,
        pivot: *mut T,
        is_less: &mut F,
    ) -> *mut T {
        unsafe {
            let scan = self.forward_scan.begin();
            let less_than_pivot = is_less(&*scan, &*pivot);
            let dest_out = self.dest.begin().add(self.num_at_dest_begin);
            let scratch_out = self.scratch_forwards_cursor.sub(self.num_at_dest_begin);
            let out = select(less_than_pivot, dest_out, scratch_out);
            if core::mem::size_of::<T>() <= core::mem::size_of::<usize>()
                && !cfg!(feature = "tracking")
            {
                // We'll overwrite a bad answer in a later iteration anyway.
                // Or not, in which case we'll never read it.
                ptr::copy(scan, dest_out, 1);
                ptr::copy(scan, scratch_out, 1);
            } else {
                ptr::copy(scan, out, 1);
            }
            self.num_at_dest_begin += less_than_pivot as usize;
            self.scratch_forwards_cursor = self.scratch_forwards_cursor.add(1);
            self.forward_scan.add_begin(1);
            out
        }
    }

    /// Partitions one element using our backward scan.
    ///
    /// SAFETY: self.backward_scan may not be empty.
    #[inline]
    unsafe fn partition_one_backward<F: Cmp<T>>(
        &mut self,
        pivot: *mut T,
        is_less: &mut F,
    ) -> *mut T {
        unsafe {
            let scan = self.backward_scan.end().sub(1);
            let less_than_pivot = is_less(&*scan, &*pivot);
            let dest_out = self
                .dest_backwards_cursor
                .add(self.num_at_scratch_end)
                .sub(1);
            let scratch_out = self.scratch.end().sub(self.num_at_scratch_end + 1);
            let out = select(less_than_pivot, scratch_out, dest_out);
            if core::mem::size_of::<T>() <= core::mem::size_of::<usize>()
                && !cfg!(feature = "tracking")
            {
                // We'll overwrite a bad answer in a later iteration anyway.
                // Or not, in which case we'll never read it.
                ptr::copy(scan, dest_out, 1);
                ptr::copy(scan, scratch_out, 1);
            } else {
                ptr::copy(scan, out, 1);
            }
            self.num_at_scratch_end += less_than_pivot as usize;
            self.dest_backwards_cursor = self.dest_backwards_cursor.sub(1);
            self.backward_scan.sub_end(1);
            out
        }
    }

    /// Partitions forwards and backwards n times.
    ///
    /// SAFETY: self.forward_scan and self.backward_scan must be at least n
    /// elements long, and respectively their prefix and suffix of n elements
    /// may not contain pivot_pos.
    unsafe fn partition_bidir_n<F: Cmp<T>>(
        &mut self,
        pivot_pos: *mut T,
        n: usize,
        is_less: &mut F,
    ) {
        // In case of a panic we must write back the pivot, which we move into a
        // local to prove to the compiler that our writes don't overwrite the
        // pivot, and thus it does not need to be reloaded.
        struct WriteBackPivot<T> {
            local_pivot: ManuallyDrop<T>,
            pivot_pos: *mut T,
        }

        impl<T> Drop for WriteBackPivot<T> {
            fn drop(&mut self) {
                unsafe {
                    ptr::copy_nonoverlapping(&mut *self.local_pivot, self.pivot_pos, 1);
                    tracking::track_copy(&mut *self.local_pivot, self.pivot_pos, 1);
                    tracking::deregister_buffer("pivot");
                }
            }
        }

        unsafe {
            let mut guard = WriteBackPivot {
                local_pivot: ManuallyDrop::new(ptr::read(pivot_pos)),
                pivot_pos,
            };
            let local_pivot_ptr = &mut *guard.local_pivot as *mut T;
            tracking::register_buffer(
                "pivot",
                MutSlice::<Unbranded, _, _>::from_pair_unchecked(
                    local_pivot_ptr,
                    local_pivot_ptr.add(1),
                ),
            );
            tracking::track_copy(pivot_pos, local_pivot_ptr, 1);
            for _ in 0..n / 4 {
                self.partition_one_forward(local_pivot_ptr, is_less);
                self.partition_one_backward(local_pivot_ptr, is_less);
                self.partition_one_forward(local_pivot_ptr, is_less);
                self.partition_one_backward(local_pivot_ptr, is_less);
                self.partition_one_forward(local_pivot_ptr, is_less);
                self.partition_one_backward(local_pivot_ptr, is_less);
                self.partition_one_forward(local_pivot_ptr, is_less);
                self.partition_one_backward(local_pivot_ptr, is_less);
            }
            for _ in 0..n % 4 {
                self.partition_one_forward(local_pivot_ptr, is_less);
                self.partition_one_backward(local_pivot_ptr, is_less);
            }
        }
    }

    /// Fully partitions the data.
    ///
    /// SAFETY: pivot_pos must point to a valid object.
    pub unsafe fn partition_bidir<F: Cmp<T>>(
        &mut self,
        mut pivot_pos: *mut T,
        is_less: &mut F,
    ) -> *mut T {
        unsafe {
            loop {
                // Our main causes of worry is that the pivot (depending on how
                // it's chosen) is in our array, and that the forward and backward
                // scans may not be of the same size. We also would like to keep
                // track of the position of our left ancestor pivot. So we
                // compute how far we can safely scan.
                let mut forward_limit = self.forward_scan.len();
                if self.forward_scan.contains(pivot_pos) {
                    forward_limit = pivot_pos.offset_from(self.forward_scan.begin()) as usize;
                }

                let mut backward_limit = self.backward_scan.len();
                if self.backward_scan.contains(pivot_pos) {
                    backward_limit = self.backward_scan.end().offset_from(pivot_pos) as usize - 1;
                }

                // We found how far we can safely scan on both sides, do that.
                let limit = forward_limit.min(backward_limit);
                self.partition_bidir_n(pivot_pos, limit, is_less);

                // We could be done, or hit one of our limits.
                if self.forward_scan.len() == 0 && self.backward_scan.len() == 0 {
                    return pivot_pos;
                } else if self.forward_scan.len() > 0 && self.forward_scan.begin() == pivot_pos {
                    pivot_pos = self.partition_one_forward(pivot_pos, is_less)
                } else if self.backward_scan.len() > 0
                    && self.backward_scan.end().sub(1) == pivot_pos
                {
                    pivot_pos = self.partition_one_backward(pivot_pos, is_less)
                } else if self.forward_scan.len() == 0 {
                    // Handle odd input sizes.
                    if self.backward_scan.len() % 2 > 0 {
                        self.partition_one_backward(pivot_pos, is_less);
                    }
                    self.forward_scan = self
                        .backward_scan
                        .split_off_begin(self.backward_scan.len() / 2);
                } else {
                    // Handle odd input sizes.
                    if self.forward_scan.len() % 2 > 0 {
                        self.partition_one_forward(pivot_pos, is_less);
                    }
                    self.backward_scan =
                        self.forward_scan.split_off_end(self.forward_scan.len() / 2);
                }
            }
        }
    }
}

impl<'l, BD: Brand, BS: Brand, T> Drop for BidirPartitionState<'l, BD, BS, T> {
    fn drop(&mut self) {
        unsafe {
            // Make sure all elements are moved into the destination.
            // We should only run this upon panicking.
            let (_dest_less, scratch_less, scratch_geq, _dest_geq) = self.take();
            let fwd = self.dest.split_off_begin(self.forward_scan.len());
            let less = self.dest.split_off_begin(scratch_less.len());
            let geq = self.dest.split_off_begin(scratch_geq.len());
            let bck = self.dest.split_off_begin(self.backward_scan.len());
            assert_abort(self.dest.len() == 0);
            // Our scans can overlap the destination, so we should copy them
            // first lest we overwrite them by accident.
            ptr::copy(self.forward_scan.begin(), fwd.begin(), fwd.len());
            ptr::copy(self.backward_scan.begin(), bck.begin(), bck.len());
            ptr::copy(scratch_less.begin(), less.begin(), less.len());
            ptr::copy(scratch_geq.begin(), geq.begin(), geq.len());
        }
    }
}

enum PartitionStrategy<T> {
    LeftWithPivot(*mut T),
    LeftIfNewPivotEquals(*mut T),
    LeftIfNewPivotEqualsCopy(T),
    RightWithNewPivot,
}

unsafe fn stable_bidir_quicksort_into<
    'l,
    BL: Brand,
    BR: Brand,
    BD: Brand,
    BS: Brand,
    T,
    F: Cmp<T>,
>(
    left: MutSlice<'l, BL, T, Init>,
    right: MutSlice<'l, BR, T, Init>,
    dest: MutSlice<'l, BD, T, Weak>,
    scratch: MutSlice<'l, BS, T, Weak>,
    partition_strategy: PartitionStrategy<T>,
    recursion_limit: usize,
    is_less: &mut F,
) {
    let n = left.len() + right.len();
    assert_abort(dest.len() == scratch.len());
    assert_abort(dest.len() == n);

    if n < crate::SMALL_SORT || recursion_limit == 0 {
        unsafe {
            let (left_dest, right_dest) = dest.clone().split_at(left.len()).unwrap_abort();
            if left.begin() != dest.begin() {
                left.move_to(left_dest.upgrade().assume_uninit());
            }
            if right.begin() != right_dest.begin() {
                right.move_to(right_dest.upgrade().assume_uninit());
            }
            let data = dest.upgrade().assume_init().always_init();

            if n < crate::SMALL_SORT {
                small_sort::small_sort(data, is_less);
            } else {
                crate::glidesort::glidesort(data, scratch.upgrade().assume_uninit(), is_less, true);
            }
            return;
        }
    }
    
    // Load left/right into state first in case pivot selection panics as our guard.
    let mut state = BidirPartitionState::new(left, right, dest.clone(), scratch.clone());
    let mut pivot_pos = if let PartitionStrategy::LeftWithPivot(p) = partition_strategy {
        p
    } else {
        select_pivot(
            state.forward_scan.borrow(),
            state.backward_scan.borrow(),
            is_less,
        )
    };
    let partition_left = match partition_strategy {
        PartitionStrategy::LeftWithPivot(_) => true,
        PartitionStrategy::LeftIfNewPivotEquals(p) => unsafe { !is_less(&*p, &*pivot_pos) },
        PartitionStrategy::LeftIfNewPivotEqualsCopy(ref p) => unsafe { !is_less(&*p, &*pivot_pos) },
        PartitionStrategy::RightWithNewPivot => false,
    };

    unsafe {
        pivot_pos = if partition_left {
            state.partition_bidir(pivot_pos, &mut cmp_from_closure(|a, b| !is_less(b, a)))
        } else {
            state.partition_bidir(pivot_pos, is_less)
        };
    }
    let (less_in_dest, less_in_scratch, geq_in_scratch, geq_in_dest) = state.take();
    core::mem::forget(state);

    // Compute recursive slices, and construct panic safety gap guards.
    let less_n = less_in_dest.len() + less_in_scratch.len();
    let geq_n = geq_in_dest.len() + geq_in_scratch.len();
    let (less_rec_dest, geq_rec_dest) = dest.clone().split_at(less_n).unwrap_abort();
    let (geq_rec_scratch, less_rec_scratch) = scratch.split_at(geq_n).unwrap_abort();

    let (less_gap, geq_gap) = {
        let (_less_in_dest, less_gap) = less_rec_dest
            .clone()
            .split_at(less_in_dest.len())
            .unwrap_abort();
        let (geq_gap, _geq_in_dest) = geq_rec_dest
            .clone()
            .split_at_end(geq_in_dest.len())
            .unwrap_abort();
        unsafe {
            (
                less_gap.upgrade().assume_uninit(),
                geq_gap.upgrade().assume_uninit(),
            )
        }
    };
    let less_in_scratch_guard = GapGuard::new_disjoint(less_in_scratch, less_gap);
    let geq_in_scratch_guard = GapGuard::new_disjoint(geq_in_scratch, geq_gap);

    // Both recursive calls are small, we can use this to overlap two slightly
    // overly large small sorts for faster smallsort sizes.
    if less_n < crate::SMALL_SORT && geq_n < crate::SMALL_SORT {
        let mut dest = unsafe {
            drop(less_in_scratch_guard);
            drop(geq_in_scratch_guard);
            dest.upgrade().assume_init().always_init()
        };

        if less_n <= 32 && less_n & 0b1000 > 0 {
            // Round up lower 3 bits.
            let round = (less_n + 0b111) & !0b111;
            small_sort::small_sort(dest.borrow().split_at(round).unwrap_abort().0, is_less);
        } else {
            small_sort::small_sort(dest.borrow().split_at(less_n).unwrap_abort().0, is_less);
        }

        if geq_n <= 32 && geq_n & 0b1000 > 0 {
            // Round up lower 3 bits.
            let round = (geq_n + 0b111) & !0b111;
            small_sort::small_sort(dest.borrow().split_at_end(round).unwrap_abort().1, is_less);
        } else {
            small_sort::small_sort(dest.borrow().split_at_end(geq_n).unwrap_abort().1, is_less);
        }
        return;
    }

    if less_n == 0 && !partition_left {
        unsafe {
            stable_bidir_quicksort_into(
                geq_in_scratch_guard.take_data(),
                geq_in_dest,
                geq_rec_dest,
                geq_rec_scratch,
                PartitionStrategy::LeftWithPivot(pivot_pos),
                recursion_limit - 1,
                is_less,
            );
        }
        return;
    }

    unsafe {
        // This ensures the two recursive calls are completely independent, for potential parallelism, even if the
        // comparison operator is invalid.
        let pivot_in_geq =
            geq_in_scratch_guard.data_weak().contains(pivot_pos) || geq_in_dest.contains(pivot_pos);
        let less_strategy = if let PartitionStrategy::LeftIfNewPivotEqualsCopy(p) = partition_strategy {
            PartitionStrategy::LeftIfNewPivotEqualsCopy(p)
        } else {
            PartitionStrategy::RightWithNewPivot
        };

        let geq_strategy = if !partition_left && T::is_copy_type() {
            PartitionStrategy::LeftIfNewPivotEqualsCopy(ptr::read(pivot_pos))
        } else if !partition_left && pivot_in_geq {
            PartitionStrategy::LeftIfNewPivotEquals(pivot_pos)
        } else {
            PartitionStrategy::RightWithNewPivot
        };

        if !partition_left {
            stable_bidir_quicksort_into(
                less_in_dest,
                less_in_scratch_guard.take_data(),
                less_rec_dest,
                less_rec_scratch,
                less_strategy,
                recursion_limit - 1,
                is_less,
            );
        }

        stable_bidir_quicksort_into(
            geq_in_scratch_guard.take_data(),
            geq_in_dest,
            geq_rec_dest,
            geq_rec_scratch,
            geq_strategy,
            recursion_limit - 1,
            is_less,
        );
    }
}

pub fn quicksort<'el, 'sc, BE: Brand, BS: Brand, T, F: Cmp<T>>(
    el: MutSlice<'el, BE, T, AlwaysInit>,
    scratch: MutSlice<'sc, BS, T, Uninit>,
    is_less: &mut F,
) -> MutSlice<'el, BE, T, AlwaysInit> {
    unsafe {
        let n = el.len();
        let logn = core::mem::size_of::<usize>() * 8 - n.leading_zeros() as usize;
        let scratch = scratch.split_at(n).unwrap_abort().0;
        let dest = el.weak();
        let (left, right) = el.raw().split_at(n / 2).unwrap_abort();
        stable_bidir_quicksort_into(
            left,
            right,
            dest.clone(),
            scratch.weak(),
            PartitionStrategy::RightWithNewPivot,
            2 * logn,
            is_less,
        );
        dest.upgrade().assume_init().always_init()
    }
}
