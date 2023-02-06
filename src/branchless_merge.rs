/*
    When merging two arrays we have six pointers, initially as such:

        left_begin              right_begin
            |                       |
            [    left      ]        [    right    ]
                           |                      |
                       left_end              right_end

         dst_begin
            |
            [           dst             ]
                                        |
                                     dst_end

    Note that in the above picture left and right are disjoint with dst, but for
    some inputs one of the two may overlap with dst.

    Logically we have two operations, a merge at the beginning, and a merge at
    the end. When disjoint both operations are valid, if left overlaps dst
    only merging at the end is valid, if right overlaps dst only merging at the
    beginning is valid.

    A merge at the beginning compares the elements at left_begin and
    right_begin. It picks the smallest of the two (breaking ties towards left
    for stability) and copies it to dst_begin, then increments the pointer it
    picked and dst_begin.

    Similarly a merge at the end compares the elements at left_end - 1 and
    right_end - 1, picks the larger of the two (breaking ties towards right)
    and copies it to dst_end - 1, then decrements the pointer it picked and
    dst_end.

    For disjoint input/destination arrays of Copy types we can be a bit more
    relaxed in our bounds checks and let the left_begin/left_end (and similarly
    for right) pointers cross. To see why, first we note that the following
    invariants always hold (and similarly for right):

        left_begin == orig_left_begin + times_left_picked_at_begin
        left_end == orig_left_end - times_left_picked_at_end
        orig_left_len = orig_left_end - orig_left_begin

    The following invariants hold for a valid comparison operator:

        orig_left_len == times_left_picked_at_begin + times_left_picked_at_end
        orig_right_len == times_right_picked_at_begin + times_right_picked_at_end

    Note that as long as we check after merging that left_begin <= left_end,
    which should hold for any valid comparison operator by the above invariants,
    we can rest assured that no element in left was ever accessed again after
    being copied, making the copies valid objects, and similarly for right. When
    left or right overlaps with dst we must make sure the begin and end pointers
    of that side never cross, otherwise we might be accessing copies before we
    know if they'll be valid.

    If this doesn't hold we accessed elements after copying them, making the
    copies invalid. In this scenario we copy all elements from the original
    arrays into the destination without any further processing. If Ord is
    violated we make no guarantees about the output order.

    Finally, we have the following invariants after k merges at the beginning
    and k merges at the end:

        times_left_picked_at_begin == k - times_right_picked_at_begin
        times_left_picked_at_end == k - times_right_picked_at_end

    Note that all the above invariants guarantee that if left/right are disjoint
    with dst and n == orig_left_len == orig_right_len, simply doing n merges at
    the beginning and n merges at the end fully merges the result.
*/

use core::marker::PhantomData;

use crate::gap_guard::GapGuard;
use crate::mut_slice::states::{AlwaysInit, Init, Uninit, Weak};
use crate::mut_slice::{Brand, MutSlice, Unbranded};
use crate::tracking::ptr;
use crate::util::*;

pub struct GapLeft; // Can write to dst at begin.
pub struct GapRight; // Can write to dst at end.
pub struct GapBoth; // Can write on both ends.

pub trait HasLeftGap {}
impl HasLeftGap for GapLeft {}
impl HasLeftGap for GapBoth {}
pub trait HasRightGap {}
impl HasRightGap for GapRight {}
impl HasRightGap for GapBoth {}

// Invariants:
//  - If G: HasLeftGap then left_begin < left_end implies left_begin is disjoint with
//    dst.begin(), and similarly for right.
//  - If G: HasRightGap then left_begin < left_end implies left_end.sub(1) is disjoint
//    with dst.end().sub(1) and similarly for right.
pub struct BranchlessMergeState<'l, 'r, 'dst, T, G> {
    dst: MutSlice<'dst, Unbranded, T, Weak>,

    // We don't use slices for these as in the disjoint case the left/right
    // pointers might cross for invalid comparison operators.
    left_begin: *mut T,
    left_end: *mut T,
    right_begin: *mut T,
    right_end: *mut T,
    _gap: G,
    _lt: PhantomData<(&'l mut (), &'r mut ())>,
}

impl<'l, 'r, 'dst, T, G> BranchlessMergeState<'l, 'r, 'dst, T, G> {
    fn new<BL, BR, BD>(
        left: MutSlice<'l, BL, T, Weak>,
        right: MutSlice<'r, BR, T, Weak>,
        dst: MutSlice<'dst, BD, T, Weak>,
        gap: G,
    ) -> Self {
        if left.len() + right.len() != dst.len() {
            abort();
        }

        Self {
            left_begin: left.begin(),
            left_end: left.end(),
            right_begin: right.begin(),
            right_end: right.end(),
            dst: dst.weak().forget_brand(),
            _gap: gap,
            _lt: PhantomData,
        }
    }
}

impl<'l, 'r, 'dst, T> BranchlessMergeState<'l, 'r, 'dst, T, GapBoth> {
    pub fn new_disjoint<BL, BR, BD>(
        left: MutSlice<'l, BL, T, Init>,
        right: MutSlice<'r, BR, T, Init>,
        dst: MutSlice<'dst, BD, T, Uninit>,
    ) -> Self {
        Self::new(left.weak(), right.weak(), dst.weak(), GapBoth)
    }
}

impl<'l, 'r, T> BranchlessMergeState<'l, 'r, 'r, T, GapLeft> {
    pub fn new_gap_left<BL: Brand, BR: Brand>(
        left: GapGuard<'l, 'r, BL, BR, T>,
        right: MutSlice<'r, BR, T, AlwaysInit>,
    ) -> Self {
        unsafe {
            // SAFETY: our drop impl will always fill the gap.
            let dst = left.gap_weak().concat(right.weak());
            let left = left.take_disjoint().0.weak();
            let right = right.raw().weak();
            Self::new(left, right, dst, GapLeft)
        }
    }
}

impl<'l, 'r, T> BranchlessMergeState<'l, 'r, 'l, T, GapRight> {
    pub fn new_gap_right<BL: Brand, BR: Brand>(
        left: MutSlice<'l, BL, T, AlwaysInit>,
        right: GapGuard<'r, 'l, BR, BL, T>,
    ) -> Self {
        unsafe {
            // SAFETY: our drop impl will always fill the gap.
            let dst = left.weak().concat(right.gap_weak());
            let left = left.raw().weak();
            let right = right.take_disjoint().0.weak();
            Self::new(left, right, dst, GapRight)
        }
    }
}

impl<'l, 'r, 'dst, T, G: HasLeftGap> BranchlessMergeState<'l, 'r, 'dst, T, G> {
    /// Merges one element from left, right into the destination, reading/writing
    /// at the begin of all the slices. If is_less panics, does nothing.
    #[inline(always)]
    pub unsafe fn branchless_merge_one_at_begin<F: Cmp<T>>(&mut self, is_less: &mut F) {
        unsafe {
            // Adding 1 and subtracting right_less gave *significantly* faster
            // codegen than adding !right_less on my Intel machine since it
            // avoided a stack spill, giving much better interleaving after
            // inlining.
            //
            // Do not touch unless you're benchmarking on multiple architectures.
            let left_scan = self.left_begin;
            let right_scan = self.right_begin;
            let right_less = is_less(&*right_scan, &*left_scan);
            let src = select(right_less, right_scan, left_scan);
            ptr::copy_nonoverlapping(src, self.dst.begin(), 1);
            self.dst.add_begin(1);
            // self.left_begin = self.left_begin.add((!right_less) as usize);
            // self.right_begin = self.right_begin.add(right_less as usize);
            self.left_begin = self.left_begin.wrapping_sub(right_less as usize); // Might go out-of-bounds.
            self.right_begin = self.right_begin.add(right_less as usize);
            self.left_begin = self.left_begin.wrapping_add(1).add(0); // Back in-bounds.
        }
    }

    /// Exactly the same as branchless_merge_one_at_begin, but does not cause
    /// out-of-bounds accesses if *one* of left, right is empty.
    #[inline]
    pub unsafe fn branchless_merge_one_at_begin_imbalance_guarded<F: Cmp<T>>(
        &mut self,
        is_less: &mut F,
    ) {
        unsafe {
            // Do not touch unless you're benchmarking on multiple architectures.
            // See branchless_merge_one_at_begin.
            let left_empty = self.left_begin == self.left_end;
            let right_nonempty = self.right_begin != self.right_end;
            let left_scan = select(left_empty, self.right_begin, self.left_begin);
            let right_scan = select(right_nonempty, self.right_begin, self.left_begin);
            let right_less = is_less(&*right_scan, &*left_scan);
            let shrink_right = right_less & right_nonempty | left_empty;

            let src = select(right_less, right_scan, left_scan);
            ptr::copy(src, self.dst.begin(), 1);
            self.dst.add_begin(1);
            self.left_begin = self.left_begin.wrapping_sub(shrink_right as usize); // Might go out-of-bounds.
            self.right_begin = self.right_begin.add(shrink_right as usize);
            self.left_begin = self.left_begin.wrapping_add(1).add(0); // Back in-bounds.
        }
    }
}

impl<'l, 'r, 'dst, T, G: HasRightGap> BranchlessMergeState<'l, 'r, 'dst, T, G> {
    /// Merges one element from left, right into the destination, reading/writing
    /// at the end of all the slices. If is_less panics, does nothing.
    #[inline(always)]
    pub unsafe fn branchless_merge_one_at_end<F: Cmp<T>>(&mut self, is_less: &mut F) {
        unsafe {
            // Do not touch unless you're benchmarking on multiple architectures.
            // See branchless_merge_one_at_begin.
            let left_scan = self.left_end.sub(1);
            let right_scan = self.right_end.sub(1);
            let right_less = is_less(&*right_scan, &*left_scan);
            let src = select(right_less, left_scan, right_scan);
            self.dst.sub_end(1);
            ptr::copy_nonoverlapping(src, self.dst.end(), 1);
            // self.left_end = self.left_end.sub(right_less as usize);
            // self.right_end = self.right_end.sub((!right_less) as usize);
            self.right_end = self.right_end.wrapping_add(right_less as usize); // Might go out-of-bounds.
            self.left_end = self.left_end.sub(right_less as usize);
            self.right_end = self.right_end.wrapping_sub(1).add(0); // Back in-bounds.
        }
    }

    /// Exactly the same as branchless_merge_one_at_end, but does not cause
    /// out-of-bounds accesses if *one* of left, right is empty.
    #[inline]
    pub unsafe fn branchless_merge_one_at_end_imbalance_guarded<F: Cmp<T>>(
        &mut self,
        is_less: &mut F,
    ) {
        unsafe {
            let left_nonempty = self.left_begin != self.left_end;
            let right_empty = self.right_begin == self.right_end;
            let left_scan = select(left_nonempty, self.left_end, self.right_end).sub(1);
            let right_scan = select(right_empty, self.left_end, self.right_end).sub(1);
            let right_less = is_less(&*right_scan, &*left_scan);
            let shrink_left = right_less & left_nonempty | right_empty;

            let src = select(right_less, left_scan, right_scan);
            self.dst.sub_end(1);
            ptr::copy(src, self.dst.end(), 1);
            self.right_end = self.right_end.wrapping_add(shrink_left as usize); // Might go out-of-bounds.
            self.left_end = self.left_end.sub(shrink_left as usize);
            self.right_end = self.right_end.wrapping_sub(1).add(0); // Back in-bounds.
        }
    }
}

impl<'l, 'r, 'dst, T, G> BranchlessMergeState<'l, 'r, 'dst, T, G> {
    /// In a symmetric merge (k == left_len == right_len) we merge at begin and
    /// at end exactly k times. We start at a total size of 2k and each merge
    /// reduces it by one. Thus if we check left_begin == left_end we also know
    /// right_begin == right_end. This indicates a successful merge, only an
    /// invalid comparison operator can violate this (safely, as long as we do
    /// not read the elements in the destination).
    #[inline(always)]
    pub fn symmetric_merge_successful(&self) -> bool {
        // Yes, not also checking right_begin == right_end for sanity was ~1%
        // slower overall.
        self.left_begin == self.left_end
    }

    /// It is safe to call a merge operation this many times.
    /// If 0 is returned the merge is effectively done since one of the sides is
    /// empty.
    pub fn num_safe_merge_ops(&self) -> usize {
        unsafe {
            let left_len = self.left_end.offset_from(self.left_begin);
            let right_len = self.right_end.offset_from(self.right_begin);
            let min = left_len.min(right_len);
            if min < 0 {
                // Our scan pointers crossed. This can only happen because
                // someone called branchless_merge_one_at_* directly, in which
                // case they should not have called this function.
                abort();
            }
            min as usize
        }
    }
}

impl<'l, 'r, 'dst, T> BranchlessMergeState<'l, 'r, 'dst, T, GapLeft> {
    #[inline(never)]
    pub fn finish_merge<F: Cmp<T>>(mut self, is_less: &mut F) {
        loop {
            let n = self.num_safe_merge_ops();
            if n == 0 {
                return;
            }

            unsafe {
                // SAFETY: we just queried that this many merge ops is safe.
                for _ in 0..n / 2 {
                    self.branchless_merge_one_at_begin(is_less);
                    self.branchless_merge_one_at_begin(is_less);
                }
                for _ in 0..n % 2 {
                    self.branchless_merge_one_at_begin(is_less);
                }
            }
        }
    }
}

impl<'l, 'r, 'dst, T> BranchlessMergeState<'l, 'r, 'dst, T, GapRight> {
    #[inline(never)]
    pub fn finish_merge<F: Cmp<T>>(mut self, is_less: &mut F) {
        loop {
            let n = self.num_safe_merge_ops();
            if n == 0 {
                return;
            }

            unsafe {
                // SAFETY: we just queried that this many merge ops is safe.
                for _ in 0..n / 2 {
                    self.branchless_merge_one_at_end(is_less);
                    self.branchless_merge_one_at_end(is_less);
                }
                for _ in 0..n % 2 {
                    self.branchless_merge_one_at_end(is_less);
                }
            }
        }
    }
}

impl<'l, 'r, 'dst, T> BranchlessMergeState<'l, 'r, 'dst, T, GapBoth> {
    #[inline(never)]
    pub fn finish_merge<F: Cmp<T>>(mut self, is_less: &mut F) {
        loop {
            let n = self.num_safe_merge_ops();
            if n == 0 {
                return;
            }

            unsafe {
                // SAFETY: we just queried that this many merge ops is safe.
                for _ in 0..n / 4 {
                    self.branchless_merge_one_at_begin(is_less);
                    self.branchless_merge_one_at_end(is_less);
                    self.branchless_merge_one_at_begin(is_less);
                    self.branchless_merge_one_at_end(is_less);
                }
                for _ in 0..n % 4 {
                    self.branchless_merge_one_at_begin(is_less);
                }
            }
        }
    }

    #[inline(never)]
    pub fn finish_merge_interleaved<F: Cmp<T>>(mut self, mut other: Self, is_less: &mut F) {
        // Interleave loops while possible.
        loop {
            let common_remaining = self.num_safe_merge_ops().min(other.num_safe_merge_ops());
            if common_remaining < 2 {
                break;
            }

            unsafe {
                // SAFETY: we just checked that this many merge operations is okay for both.
                for _ in 0..common_remaining / 2 {
                    self.branchless_merge_one_at_begin(is_less);
                    other.branchless_merge_one_at_begin(is_less);
                    self.branchless_merge_one_at_end(is_less);
                    other.branchless_merge_one_at_end(is_less);
                }
            }
        }

        self.finish_merge(is_less);
        other.finish_merge(is_less);
    }
}

impl<'l, 'r, 'dst, T, G> Drop for BranchlessMergeState<'l, 'r, 'dst, T, G> {
    fn drop(&mut self) {
        unsafe {
            // Extra sanity check.
            let left_len = self
                .left_end
                .offset_from(self.left_begin)
                .try_into()
                .unwrap_abort();
            let right_len = self
                .right_end
                .offset_from(self.right_begin)
                .try_into()
                .unwrap_abort();
            assert_abort(left_len + right_len == self.dst.len());

            // SAFETY: ok by our sanity check.
            let dst_begin = self.dst.begin();
            let mid = dst_begin.add(left_len);
            ptr::copy(self.left_begin, dst_begin, left_len);
            ptr::copy(self.right_begin, mid, right_len);
        }
    }
}
