// For physical merges we have two main goals:
//
//  1. Reduce unnecessary data movement moving into/from scratch space. Ideally
//     every move is part of a merge operation. We do this by combining multiple
//     merges in glidesort's logical merge structure, and on the physical level
//     by splitting merges into smaller merges.
//
//  2. We want to combine multiple independent merges into interleaved loops to
//     use instruction-level parallelism and hide critical path data dependecy
//     latencies.

use crate::branchless_merge::BranchlessMergeState;
use crate::gap_guard::GapGuard;
use crate::merge_reduction::{merge_splitpoints, shrink_stable_merge};
use crate::mut_slice::states::{AlwaysInit, Init, Uninit};
use crate::mut_slice::{Brand, MutSlice};
use crate::tracking::ptr;
use crate::util::*;

/// Merges adjacent runs left, right using the given scratch space.
///
/// Panics if if_less does, aborts if left, right aren't contiguous.
pub(crate) fn physical_merge<'el, 'sc, BE: Brand, BS: Brand, T, F: Cmp<T>>(
    mut left: MutSlice<'el, BE, T, AlwaysInit>,
    mut right: MutSlice<'el, BE, T, AlwaysInit>,
    mut scratch: MutSlice<'sc, BS, T, Uninit>,
    is_less: &mut F,
) -> MutSlice<'el, BE, T, AlwaysInit> {
    let ret = left.weak().concat(right.weak());

    while let Some((left_shrink, right_shrink)) =
        shrink_stable_merge(left.as_mut_slice(), right.as_mut_slice(), is_less)
    {
        // Shrink.
        left = left.split_at(left_shrink).unwrap().1;
        right = right.split_at(right_shrink).unwrap().0;

        // Split into parallel merge with left1.len() == right0.len().
        let (lsplit, rsplit) =
            merge_splitpoints(left.as_mut_slice(), right.as_mut_slice(), is_less);
        let (left0, left1) = left.split_at(lsplit).unwrap_abort();
        let (right0, right1) = right.split_at(rsplit).unwrap_abort();

        // Logically we swap left1 and right0 and then merge (left0, left1) and (right0, right1).
        // In reality we can often avoid the explicit swap by renaming scratch buffers.
        if let Some((left1_scratch, _)) = scratch.borrow().split_at(left1.len()) {
            unsafe {
                // SAFETY: should a panic occur first the left1_gap is filled
                // by merge_right_gap, consuming right0, then this gap is filled
                // by the left1_with_right0_gap guard.
                let (left1_gap, left1_scratch) = left1.raw().move_to(left1_scratch);
                let left1_with_right0_gap =
                    GapGuard::new_unchecked(left1_scratch.weak(), right0.weak());
                let right0_with_left1_gap = GapGuard::new_disjoint(right0.raw(), left1_gap);
                merge_right_gap(left0, right0_with_left1_gap, is_less);
                merge_left_gap(left1_with_right0_gap, right1, is_less);
                break;
            }
        } else {
            unsafe {
                // Same as left1.as_mut_slice().swap_with_slice(right0.as_mut_slice());
                // Uses ptr for tracking purposes.
                ptr::swap_nonoverlapping(left1.weak().begin(), right0.weak().begin(), left1.len());
            }
            physical_merge(right0, right1, scratch.borrow(), is_less);
        }

        (left, right) = (left0, left1);
    }

    // SAFETY: we never permanently moved any elements out of our range.
    unsafe { ret.upgrade().assume_init().always_init() }
}

/// Merges sorted runs r0, r1, r2 using the given scratch space.
///
/// Panics if_less does, aborts if r0, r1, r2 aren't contiguous.
pub(crate) fn physical_triple_merge<'el, 'sc, BE: Brand, BS: Brand, T, F: Cmp<T>>(
    r0: MutSlice<'el, BE, T, AlwaysInit>,
    r1: MutSlice<'el, BE, T, AlwaysInit>,
    r2: MutSlice<'el, BE, T, AlwaysInit>,
    scratch: MutSlice<'sc, BS, T, Uninit>,
    is_less: &mut F,
) -> MutSlice<'el, BE, T, AlwaysInit> {
    unsafe {
        // SAFETY: our only constraint and reason this function body is unsafe is
        // that the gap guards returned by try_merge_into_scratch may not be forgotten.

        // Merge r0, r1 or r1, r2 first?
        if r0.len() < r2.len() {
            match try_merge_into_scratch(r0, r1, scratch, is_less) {
                (Ok(r0r1), _rest_scratch) => merge_left_gap(r0r1, r2, is_less),
                (Err((r0, r1)), mut scratch) => {
                    let r0r1 = physical_merge(r0, r1, scratch.borrow(), is_less);
                    physical_merge(r0r1, r2, scratch, is_less)
                }
            }
        } else {
            match try_merge_into_scratch(r1, r2, scratch, is_less) {
                (Ok(r1r2), _rest_scratch) => merge_right_gap(r0, r1r2, is_less),
                (Err((r1, r2)), mut scratch) => {
                    let r1r2 = physical_merge(r1, r2, scratch.borrow(), is_less);
                    physical_merge(r0, r1r2, scratch, is_less)
                }
            }
        }
    }
}

/// Merges sorted runs r0, r1, r2, r3 using the given scratch space.
///
/// Panics if is_less does, aborts if r0, r1, r2, r3 aren't contiguous.
pub(crate) fn physical_quad_merge<'el, 'sc, BE: Brand, BS: Brand, T, F: Cmp<T>>(
    r0: MutSlice<'el, BE, T, AlwaysInit>,
    r1: MutSlice<'el, BE, T, AlwaysInit>,
    r2: MutSlice<'el, BE, T, AlwaysInit>,
    r3: MutSlice<'el, BE, T, AlwaysInit>,
    mut scratch: MutSlice<'sc, BS, T, Uninit>,
    is_less: &mut F,
) -> MutSlice<'el, BE, T, AlwaysInit> {
    let left_len = r0.len() + r1.len();
    let right_len = r2.len() + r3.len();

    if let Some((scratch, _)) = scratch.borrow().split_at(left_len + right_len) {
        unsafe {
            let dst = r0
                .weak()
                .concat(r1.weak())
                .concat(r2.weak())
                .concat(r3.weak());
            let guard = GapGuard::new_unchecked(scratch.weak(), dst);
            double_merge_into(r0.raw(), r1.raw(), r2.raw(), r3.raw(), scratch, is_less);
            let (left, right) = guard.split_at(left_len).unwrap_abort();
            return merge_into_gap(left, right, is_less).always_init();
        }
    }

    unsafe {
        // Try to merge the bigger pair into scratch first. This guarantees that if the
        // bigger one fits but the smaller one doesn't we can use the old space of
        // the bigger one as scratch space while merging the smaller one.
        let (left_merge, right_merge);
        if left_len >= right_len {
            (left_merge, scratch) = try_merge_into_scratch(r0, r1, scratch, is_less);
            (right_merge, scratch) = try_merge_into_scratch(r2, r3, scratch, is_less);
        } else {
            (right_merge, scratch) = try_merge_into_scratch(r2, r3, scratch, is_less);
            (left_merge, scratch) = try_merge_into_scratch(r0, r1, scratch, is_less);
        };

        match (left_merge, right_merge) {
            (Ok(_left), Ok(_right)) => unreachable!(),

            (Ok(mut left), Err((r2, r3))) => {
                // We can use the gap from left to help merge r2, r3. It must be
                // bigger than whatever's left of the original scratch space, otherwise
                // both would've fit.
                let right = physical_merge(r2, r3, left.borrow_gap(), is_less);
                merge_left_gap(left, right, is_less)
            }

            (Err((r0, r1)), Ok(mut right)) => {
                // Vice versa.
                let left = physical_merge(r0, r1, right.borrow_gap(), is_less);
                merge_right_gap(left, right, is_less)
            }

            (Err((r0, r1)), Err((r2, r3))) => {
                let left = physical_merge(r0, r1, scratch.borrow(), is_less);
                let right = physical_merge(r2, r3, scratch.borrow(), is_less);
                physical_merge(left, right, scratch, is_less)
            }
        }
    }
}

/// Merges sorted runs left, right, using the given gap which must be equal in
/// size to left and just before right (otherwise we abort).
///
/// Should a panic occur all input is written to left.weak_gap().concat(right),
/// in an unspecified order.
pub(crate) fn merge_left_gap<'l, 'r, BL: Brand, BR: Brand, T, F: Cmp<T>>(
    mut left: GapGuard<'l, 'r, BL, BR, T>,
    mut right: MutSlice<'r, BR, T, AlwaysInit>,
    is_less: &mut F,
) -> MutSlice<'r, BR, T, AlwaysInit> {
    let ret = left.gap_weak().concat(right.weak());
    loop {
        if left.len().min(right.len()) >= crate::MERGE_SPLIT_THRESHOLD {
            let (lsplit, rsplit) =
                merge_splitpoints(left.as_mut_slice(), right.as_mut_slice(), is_less);
            let (left0, left1) = left.split_at(lsplit).unwrap_abort();
            let (right0, right1) = right.split_at(rsplit).unwrap_abort();

            unsafe {
                // SAFETY: merge_into_gap ensures right0 moves into left1_gap.
                // Afterwards the other gap guard ensures left1_data moves into
                // the gap from right0.
                let (left1_data, left1_gap) = left1.take_disjoint();
                let left1_with_right0_gap =
                    GapGuard::new_unchecked(left1_data.weak(), right0.weak());
                let right0_with_left1_gap = GapGuard::new_disjoint(right0.raw(), left1_gap);
                merge_into_gap(left0, right0_with_left1_gap, is_less);
                left = left1_with_right0_gap;
                right = right1;
            }
        } else {
            let merge_state = BranchlessMergeState::new_gap_left(left, right);
            merge_state.finish_merge(is_less);
            return unsafe { ret.upgrade().assume_init().always_init() };
        }
    }
}

/// Merges sorted runs left, right, using the given gap which must be equal in
/// size to right and just after left (otherwise we abort).
///
/// Should a panic occur all input is written to left.concat(gap), in an
/// unspecified order.
pub(crate) fn merge_right_gap<'l, 'r, BL: Brand, BR: Brand, T, F: Cmp<T>>(
    mut left: MutSlice<'l, BL, T, AlwaysInit>,
    mut right: GapGuard<'r, 'l, BR, BL, T>,
    is_less: &mut F,
) -> MutSlice<'l, BL, T, AlwaysInit> {
    let ret = left.weak().concat(right.gap_weak());
    loop {
        if left.len().min(right.len()) >= crate::MERGE_SPLIT_THRESHOLD {
            let (lsplit, rsplit) =
                merge_splitpoints(left.as_mut_slice(), right.as_mut_slice(), is_less);
            let (left0, left1) = left.split_at(lsplit).unwrap_abort();
            let (right0, right1) = right.split_at(rsplit).unwrap_abort();

            unsafe {
                // SAFETY: merge_into_gap ensures left1 moves into right0_gap.
                // Afterwards the other gap guard ensures right0_data moves into
                // the gap from left1.
                let (right0_data, right0_gap) = right0.take_disjoint();
                let right0_with_left1_gap =
                    GapGuard::new_unchecked(right0_data.weak(), left1.weak());
                let left1_with_right0_gap = GapGuard::new_disjoint(left1.raw(), right0_gap);
                merge_into_gap(left1_with_right0_gap, right1, is_less);
                left = left0;
                right = right0_with_left1_gap;
            }
        } else {
            let merge_state = BranchlessMergeState::new_gap_right(left, right);
            merge_state.finish_merge(is_less);
            return unsafe { ret.upgrade().assume_init().always_init() };
        }
    }
}

// Merges consecutive runs left, right into the given scratch space. Returns an
// object that would move the elements back into the gap if it were to be
// dropped, use res.take() if you want the actual result.
//
// Returns either the merge result if successful, or the original two slices.
// Also returns what is left of the scratch space.
//
/// Panics if_less does, aborts if left, right aren't contiguous. If a panic
/// occurs all elements are returned to left, right.
///
/// SAFETY: the returned gap guard may not be forgotten.
pub(crate) unsafe fn try_merge_into_scratch<'el, 'sc, BE: Brand, BS: Brand, T, F: Cmp<T>>(
    left: MutSlice<'el, BE, T, AlwaysInit>,
    right: MutSlice<'el, BE, T, AlwaysInit>,
    mut scratch: MutSlice<'sc, BS, T, Uninit>,
    is_less: &mut F,
) -> (
    Result<
        GapGuard<'sc, 'el, BS, BE, T>,
        (
            MutSlice<'el, BE, T, AlwaysInit>,
            MutSlice<'el, BE, T, AlwaysInit>,
        ),
    >,
    MutSlice<'sc, BS, T, Uninit>,
) {
    let gap = left.weak().concat(right.weak());
    if scratch.len() >= gap.len() {
        unsafe {
            let dst = scratch.split_off_begin(gap.len());
            // SAFETY: Should something panic all elements first get moved into
            // the scratch before being moved back by ret's gap guard.
            let ret = GapGuard::new_unchecked(dst.weak(), gap.weak());
            let (left_scratch, right_scratch) = dst.split_at(left.len()).unwrap_abort();
            let left = GapGuard::new_disjoint(left.raw(), left_scratch);
            let right = GapGuard::new_disjoint(right.raw(), right_scratch);
            merge_into_gap(left, right, is_less);
            (Ok(ret), scratch)
        }
    } else {
        (Err((left, right)), scratch)
    }
}

/// Merges sorted runs left, right into their gaps, which must be contiguous.
///
/// Should a panic occur the gap is filled.
pub(crate) fn merge_into_gap<'src, 'dst, BL: Brand, BR: Brand, BD: Brand, T, F: Cmp<T>>(
    mut left: GapGuard<'src, 'dst, BL, BD, T>,
    mut right: GapGuard<'src, 'dst, BR, BD, T>,
    is_less: &mut F,
) -> MutSlice<'dst, BD, T, Init> {
    let ret = left.gap_weak().concat(right.gap_weak());
    if left.len().min(right.len()) >= crate::MERGE_SPLIT_THRESHOLD {
        let (lsplit, rsplit) =
            merge_splitpoints(left.as_mut_slice(), right.as_mut_slice(), is_less);

        unsafe {
            // These merge states will ensure that in a panic we write all output to dest.
            let (left_data, left_gap) = left.take_disjoint();
            let (right_data, right_gap) = right.take_disjoint();
            let (left0, left1) = left_data.split_at(lsplit).unwrap_abort();
            let (right0, right1) = right_data.split_at(rsplit).unwrap_abort();
            double_merge_into(
                left0,
                right0,
                left1,
                right1,
                left_gap.concat(right_gap),
                is_less,
            );
        }
    } else {
        unsafe {
            let merge_state = BranchlessMergeState::new_disjoint(
                left.take_disjoint().0,
                right.take_disjoint().0,
                ret.clone().upgrade().assume_uninit(),
            );
            merge_state.finish_merge(is_less);
        }
    }

    unsafe { ret.upgrade().assume_init() }
}

/// Merges sorted runs left0, left1, right0, right1 into the destination.
///
/// Should a panic occur all elements are moved into the destination.
pub(crate) fn double_merge_into<'src, 'dst, BL0, BL1, BR0, BR1, BD, T, F: Cmp<T>>(
    left0: MutSlice<'src, BL0, T, Init>,
    left1: MutSlice<'src, BL1, T, Init>,
    right0: MutSlice<'src, BR0, T, Init>,
    right1: MutSlice<'src, BR1, T, Init>,
    dest: MutSlice<'dst, BD, T, Uninit>,
    is_less: &mut F,
) -> MutSlice<'dst, BD, T, Init> {
    let ret = dest.weak();
    let left_len = left0.len() + left1.len();
    let (left_dest, right_dest) = dest.split_at(left_len).unwrap_abort();
    // These merge states will ensure that in a panic we write all output to dest.
    let left_merge_state = BranchlessMergeState::new_disjoint(left0, left1, left_dest);
    let right_merge_state = BranchlessMergeState::new_disjoint(right0, right1, right_dest);
    left_merge_state.finish_merge_interleaved(right_merge_state, is_less);
    unsafe { ret.upgrade().assume_init() }
}
