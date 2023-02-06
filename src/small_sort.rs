use crate::branchless_merge::BranchlessMergeState;
use crate::mut_slice::states::{AlwaysInit, Init, MaybeInit, Uninit, Weak};
use crate::mut_slice::{with_stack_scratch, Brand, MutSlice, Unbranded};
use crate::tracking::ptr;
use crate::util::*;

pub fn small_sort<'l, B: Brand, T, F: Cmp<T>>(el: MutSlice<'l, B, T, AlwaysInit>, is_less: &mut F) {
    block_insertion_sort(el, is_less)
}

/// Sorts four elements from src into dst.
///
/// SAFETY: src and dst may not overlap.
#[inline(always)]
pub unsafe fn sort4_raw<T, F: Cmp<T>>(srcp: *mut T, dstp: *mut T, is_less: &mut F) {
    unsafe {
        // Stably create two pairs a <= b and c <= d.
        let c1 = is_less(&*srcp.add(1), &*srcp) as usize;
        let c2 = is_less(&*srcp.add(3), &*srcp.add(2)) as usize;
        let a = srcp.add(c1);
        let b = srcp.add(c1 ^ 1);
        let c = srcp.add(2 + c2);
        let d = srcp.add(2 + (c2 ^ 1));

        // Compare (a, c) and (b, d) to identify max/min. We're left with two
        // unknown elements, but because we are a stable sort we must know which
        // one is leftmost and which one is rightmost.
        // c3, c4 | min max unk_left unk_right
        //  0,  0 |  a   d    b         c
        //  0,  1 |  a   b    c         d
        //  1,  0 |  c   d    a         b
        //  1,  1 |  c   b    a         d
        let c3 = is_less(&*c, &*a);
        let c4 = is_less(&*d, &*b);
        let min = select(c3, c, a);
        let max = select(c4, b, d);
        let unk_left = select(c3, a, select(c4, c, b));
        let unk_right = select(c4, d, select(c3, b, c));

        // Sort the last two unknown elements.
        let c5 = is_less(&*unk_right, &*unk_left);
        let lo = select(c5, unk_right, unk_left);
        let hi = select(c5, unk_left, unk_right);

        ptr::copy_nonoverlapping(min, dstp, 1);
        ptr::copy_nonoverlapping(lo, dstp.add(1), 1);
        ptr::copy_nonoverlapping(hi, dstp.add(2), 1);
        ptr::copy_nonoverlapping(max, dstp.add(3), 1);
    }
}

/// A helper struct for creating sorts of small 2^n sized arrays. It ensures
/// that if the comparison operator panics all elements are moved back to the
/// original src location.
struct Pow2SmallSort<'l, BR, T> {
    orig_src: MutSlice<'l, BR, T, Weak>,
    cur_src: MutSlice<'l, Unbranded, T, Init>,
    cur_dst: MutSlice<'l, Unbranded, T, Uninit>,
}

impl<'l, BR, T> Pow2SmallSort<'l, BR, T> {
    pub fn new<BD>(src: MutSlice<'l, BR, T, Init>, dst: MutSlice<'l, BD, T, Uninit>) -> Self {
        assert_abort(src.len() == dst.len());
        Self {
            orig_src: src.weak(),
            cur_src: src.forget_brand(),
            cur_dst: dst.forget_brand(),
        }
    }
}

impl<'l, BR, T> Pow2SmallSort<'l, BR, T> {
    // Set a new output destination. The current source must be exhausted.
    #[inline]
    pub fn set_new_dst<BND>(&mut self, new_dst: MutSlice<'l, BND, T, Uninit>) {
        unsafe {
            // SAFETY: because the old source location is empty, the old
            // destination must now be filled with initialized elements.
            assert_abort(self.cur_src.len() == 0);
            let mut old_dst = core::mem::replace(&mut self.cur_dst, new_dst.forget_brand());
            old_dst.sub_begin(self.orig_src.len());
            self.cur_src = old_dst.assume_init();
        }
    }

    // Swap the source and destination. The current source must be exhausted.
    #[inline]
    pub fn swap_src_dst(&mut self) {
        unsafe {
            // SAFETY: because the old source location is empty, the old
            // destination must now be filled with initialized elements.
            assert_abort(self.cur_src.len() == 0);
            let mut new_dst = self.cur_src.weak().upgrade().assume_uninit();
            new_dst.sub_begin(self.orig_src.len());
            self.set_new_dst(new_dst);
        }
    }

    // Sort N/4 four-element arrays into N/4 four-element arrays from src into dst.
    #[inline]
    pub fn sort_groups_of_four_from_src_to_dst<const N: usize, F: Cmp<T>>(
        &mut self,
        is_less: &mut F,
    ) {
        unsafe {
            assert_abort(N % 4 == 0 && N == self.cur_src.len());
            for _ in 0..N / 4 {
                sort4_raw(self.cur_src.begin(), self.cur_dst.begin(), is_less);
                self.cur_src.add_begin(4);
                self.cur_dst.add_begin(4);
            }
        }
    }

    /// Merge two k-element arrays into one 2k-element array from src into dst.
    pub fn final_merge_from_dst_into<'dst: 'l, const N: usize, BD, F: Cmp<T>>(
        mut self,
        dst: MutSlice<'dst, BD, T, Uninit>,
        is_less: &mut F,
    ) -> MutSlice<'dst, BD, T, Init> {
        unsafe {
            assert_abort(N % 4 == 0 && dst.len() == N);
            let k = N / 2;
            let ret = dst.weak();
            self.set_new_dst(dst);

            // The BranchlessMergeState will ensure things are moved to dest should
            // a panic occur, after which our drop handler will move it back to
            // orig_src.
            let backup_src = self.cur_src.weak();
            let backup_dst = self.cur_dst.weak();
            let left = self.cur_src.split_off_begin(k);
            let right = self.cur_src.split_off_begin(k);
            let dst = self.cur_dst.split_off_begin(2 * k);
            let mut merge_state = BranchlessMergeState::new_disjoint(left, right, dst);

            if T::may_call_ord_on_copy() {
                for _ in 0..k {
                    merge_state.branchless_merge_one_at_begin(is_less);
                    merge_state.branchless_merge_one_at_end(is_less);
                }

                if !merge_state.symmetric_merge_successful() {
                    // Bad comparison operator, just copy over input.
                    ptr::copy(backup_src.upgrade().begin(), backup_dst.begin(), N);
                }
            } else {
                for _ in 0..k / 2 {
                    merge_state.branchless_merge_one_at_begin(is_less);
                    merge_state.branchless_merge_one_at_end(is_less);
                }
                for _ in 0..k / 2 {
                    // For Copy types these could be unguarded. All memory accesses
                    // are in-bounds regardless, without the guard we would however
                    // call the comparison operator on copies we would forget.
                    merge_state.branchless_merge_one_at_begin_imbalance_guarded(is_less);
                    merge_state.branchless_merge_one_at_end_imbalance_guarded(is_less);
                }
            }

            // All elements are properly initialized in dst.
            core::mem::forget(merge_state);
            core::mem::forget(self);
            ret.upgrade().assume_init()
        }
    }

    /// Merge four k-element arrays into two k-element arrays from src into dst.
    #[inline(never)]
    pub fn double_merge_from_src_to_dst<const N: usize, F: Cmp<T>>(&mut self, is_less: &mut F) {
        unsafe {
            assert_abort(N % 8 == 0 && N <= self.cur_src.len());
            let k = N / 4;

            // The BranchlessMergeState will ensure things are moved to dest should
            // a panic occur, after which our drop handler will move it back to
            // orig_src.
            let backup_src = self.cur_src.weak();
            let backup_dst = self.cur_dst.weak();
            let left0 = self.cur_src.split_off_begin(k);
            let left1 = self.cur_src.split_off_begin(k);
            let right0 = self.cur_src.split_off_begin(k);
            let right1 = self.cur_src.split_off_begin(k);
            let left_dst = self.cur_dst.split_off_begin(2 * k);
            let right_dst = self.cur_dst.split_off_begin(2 * k);
            let mut left_merge = BranchlessMergeState::new_disjoint(left0, left1, left_dst);
            let mut right_merge = BranchlessMergeState::new_disjoint(right0, right1, right_dst);

            if T::may_call_ord_on_copy() {
                for _ in 0..k {
                    left_merge.branchless_merge_one_at_begin(is_less);
                    right_merge.branchless_merge_one_at_begin(is_less);
                    left_merge.branchless_merge_one_at_end(is_less);
                    right_merge.branchless_merge_one_at_end(is_less);
                }

                if !left_merge.symmetric_merge_successful()
                    || !right_merge.symmetric_merge_successful()
                {
                    // Bad comparison operator, just copy over input.
                    ptr::copy(backup_src.upgrade().begin(), backup_dst.begin(), N);
                }
            } else {
                for _ in 0..k / 2 {
                    left_merge.branchless_merge_one_at_begin(is_less);
                    right_merge.branchless_merge_one_at_begin(is_less);
                    left_merge.branchless_merge_one_at_end(is_less);
                    right_merge.branchless_merge_one_at_end(is_less);
                }
                for _ in 0..k / 2 {
                    // For Copy types these could be unguarded. All memory accesses
                    // are in-bounds regardless, without the guard we would however
                    // call the comparison operator on copies we would forget.
                    left_merge.branchless_merge_one_at_begin_imbalance_guarded(is_less);
                    right_merge.branchless_merge_one_at_begin_imbalance_guarded(is_less);
                    left_merge.branchless_merge_one_at_end_imbalance_guarded(is_less);
                    right_merge.branchless_merge_one_at_end_imbalance_guarded(is_less);
                }
            }

            // Merging fully done.
            core::mem::forget(left_merge);
            core::mem::forget(right_merge);
        }
    }
}

impl<'l, BR, T> Drop for Pow2SmallSort<'l, BR, T> {
    #[cold]
    fn drop(&mut self) {
        unsafe {
            // Put all elements back in orig_src.
            let num_in_src = self.cur_src.len();
            let num_in_dst = self.orig_src.len() - num_in_src;
            ptr::copy(self.cur_src.begin(), self.orig_src.begin(), num_in_src);
            ptr::copy(
                self.cur_dst.begin().sub(num_in_dst),
                self.orig_src.begin().add(num_in_src),
                num_in_dst,
            );
        }
    }
}

fn sort4_into<'src, 'dst, 'tmp, BS: Brand, BD: Brand, BT: Brand, T, F: Cmp<T>>(
    src: MutSlice<'src, BS, T, Init>,
    dst: MutSlice<'dst, BD, T, Weak>,
    scratch: MutSlice<'tmp, BT, T, Uninit>,
    is_less: &mut F,
) -> MutSlice<'dst, BD, T, Init> {
    unsafe {
        sort4_raw(src.begin(), scratch.begin(), is_less);
        core::mem::forget(src);
        scratch
            .assume_init()
            .move_to(dst.upgrade().assume_uninit())
            .1
    }
}

fn sort8_into<'src, 'dst, 'tmp, BS: Brand, BD: Brand, BT: Brand, T, F: Cmp<T>>(
    src: MutSlice<'src, BS, T, Init>,
    dst: MutSlice<'dst, BD, T, Weak>,
    scratch: MutSlice<'tmp, BT, T, Uninit>,
    is_less: &mut F,
) -> MutSlice<'dst, BD, T, Init> {
    let mut sort = Pow2SmallSort::new(src, scratch);
    sort.sort_groups_of_four_from_src_to_dst::<8, F>(is_less);
    let dst = unsafe { dst.upgrade().assume_uninit() };
    sort.final_merge_from_dst_into::<8, BD, F>(dst, is_less)
}

fn sort16_into<'src, 'dst, 'tmp, BS: Brand, BD: Brand, BT: Brand, T, F: Cmp<T>>(
    src: MutSlice<'src, BS, T, Init>,
    dst: MutSlice<'dst, BD, T, Weak>,
    scratch: MutSlice<'tmp, BT, T, Uninit>,
    is_less: &mut F,
) -> MutSlice<'dst, BD, T, Init> {
    let (scratch0, scratch1) = scratch.split_at(16).unwrap_abort();
    let mut sort = Pow2SmallSort::new(src, scratch0);
    sort.sort_groups_of_four_from_src_to_dst::<16, F>(is_less);
    sort.set_new_dst(scratch1);
    sort.double_merge_from_src_to_dst::<16, F>(is_less);
    let dst = unsafe { dst.upgrade().assume_uninit() };
    sort.final_merge_from_dst_into::<16, BD, F>(dst, is_less)
}

fn sort32_into<'src, 'dst, 'tmp, BS: Brand, BD: Brand, BT: Brand, T, F: Cmp<T>>(
    src: MutSlice<'src, BS, T, Init>,
    dst: MutSlice<'dst, BD, T, Weak>,
    scratch: MutSlice<'tmp, BT, T, Uninit>,
    is_less: &mut F,
) -> MutSlice<'dst, BD, T, Init> {
    let (scratch0, scratch1) = scratch.split_at(32).unwrap_abort();
    let mut sort = Pow2SmallSort::new(src, scratch0);
    sort.sort_groups_of_four_from_src_to_dst::<32, F>(is_less);
    sort.set_new_dst(scratch1);
    sort.double_merge_from_src_to_dst::<16, F>(is_less);
    sort.double_merge_from_src_to_dst::<16, F>(is_less);
    sort.swap_src_dst();
    sort.double_merge_from_src_to_dst::<32, F>(is_less);
    let dst = unsafe { dst.upgrade().assume_uninit() };
    sort.final_merge_from_dst_into::<32, BD, F>(dst, is_less)
}

// A helper function that inserts sorted run src into dst, dst_hole, where the
// hole is initially directly after dst. On a panic the hole is closed.
struct BlockInserter<'l, BS, BD, T> {
    src: MutSlice<'l, BS, T, Init>,
    dst: MutSlice<'l, BD, T, MaybeInit>,
    hole_begin: *mut T,
}

impl<'l, BS, BD: Brand, T> BlockInserter<'l, BS, BD, T> {
    fn new(
        src: MutSlice<'l, BS, T, Init>,
        dst: MutSlice<'l, BD, T, Init>,
        dst_hole: MutSlice<'l, BD, T, Uninit>,
    ) -> Self {
        assert_abort(src.len() == dst_hole.len());
        let hole_begin = dst_hole.begin();
        let dst = dst.allow_maybe_init().concat(dst_hole.allow_maybe_init());
        Self {
            src,
            dst,
            hole_begin,
        }
    }

    fn insert<F: Cmp<T>>(mut self, is_less: &mut F) {
        unsafe {
            while self.src.len() > 0 {
                let p = self.src.end().sub(1);
                while self.hole_begin != self.dst.begin() && is_less(&*p, &*self.hole_begin.sub(1))
                {
                    self.hole_begin = self.hole_begin.sub(1);
                    self.dst.sub_end(1);
                    ptr::copy_nonoverlapping(self.hole_begin, self.dst.end(), 1);
                }

                self.src.sub_end(1);
                self.dst.sub_end(1);
                ptr::copy_nonoverlapping(p, self.dst.end(), 1);
            }

            core::mem::forget(self);
        }
    }
}

impl<'l, BS, BD, T> Drop for BlockInserter<'l, BS, BD, T> {
    #[inline(never)]
    #[cold]
    fn drop(&mut self) {
        unsafe {
            ptr::copy_nonoverlapping(self.src.begin(), self.hole_begin, self.src.len());
        }
    }
}

fn partial_sort_into<'src, 'dst, BS: Brand, BD: Brand, T, F: Cmp<T>>(
    mut src: MutSlice<'src, BS, T, Init>,
    mut dst: MutSlice<'dst, BD, T, Weak>,
    is_less: &mut F,
) -> MutSlice<'dst, BD, T, Init> {
    with_stack_scratch::<64, T, _, _>("partial-sort-into-scratch", |mut scratch| {
        let n = src.len();
        assert_abort(dst.len() >= n.min(32));
        if n >= 32 {
            sort32_into(
                src.split_off_begin(32),
                dst.split_off_begin(32),
                scratch,
                is_less,
            )
        } else if n >= 16 {
            sort16_into(
                src.split_off_begin(16),
                dst.split_off_begin(16),
                scratch.split_off_begin(32), // Yes, 32.
                is_less,
            )
        } else if n >= 8 {
            sort8_into(
                src.split_off_begin(8),
                dst.split_off_begin(8),
                scratch.split_off_begin(8),
                is_less,
            )
        } else if n >= 4 {
            sort4_into(
                src.split_off_begin(4),
                dst.split_off_begin(4),
                scratch.split_off_begin(4),
                is_less,
            )
        } else if n >= 2 {
            unsafe {
                let first = src.begin();
                let second = src.begin().add(1);
                if is_less(&*second, &*first) {
                    ptr::swap_nonoverlapping(first, second, 1);
                }
                ptr::copy(first, dst.begin(), 1);
                ptr::copy(second, dst.begin().add(1), 1);
                dst.split_off_begin(2).upgrade().assume_init()
            }
        } else {
            unsafe {
                ptr::copy(src.begin(), dst.begin(), 1);
                dst.split_off_begin(1).upgrade().assume_init()
            }
        }
    })
}

pub fn block_insertion_sort<'l, B: Brand, T, F: Cmp<T>>(
    mut el: MutSlice<'l, B, T, AlwaysInit>,
    is_less: &mut F,
) {
    let n = el.len();
    if n <= 1 {
        return;
    }

    unsafe {
        let el_weak = el.weak();
        let n = el.len();
        let mut num_sorted = partial_sort_into(el.borrow().raw(), el_weak, is_less).len();

        with_stack_scratch::<32, T, _, _>("block-insertion-sort-scratch", |scratch| {
            while num_sorted < n {
                let (sorted, unsorted) = el.borrow().split_at(num_sorted).unwrap_abort();
                let mut unsorted_weak = unsorted.weak();
                let in_scratch = partial_sort_into(unsorted.raw(), scratch.weak(), is_less);
                num_sorted += in_scratch.len();
                let gap = unsorted_weak.split_off_begin(in_scratch.len());
                BlockInserter::new(in_scratch, sorted.raw(), gap.upgrade().assume_uninit())
                    .insert(is_less);
            }
        });
    }
}
