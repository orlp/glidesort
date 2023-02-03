use crate::util::*;

/// Shrinks a stable merge of two slices to a (potentially) smaller
/// case. Returns indices (l, r) such that (left[l..], right[..r]) is the
/// smaller case, or returns None if done.
///
/// Panics if if_less does.
pub fn shrink_stable_merge<T, F: Cmp<T>>(
    left: &[T],
    right: &[T],
    is_less: &mut F,
) -> Option<(usize, usize)> {
    // Is neither left or right empty?
    if let (Some(l_last), Some(r_first)) = (left.last(), right.first()) {
        // Are we already completely sorted?
        if is_less(r_first, l_last) {
            // Find extremal elements that end up in a different position when
            // merged.
            // TODO: potential optimization here, check first, say, 16 elements
            // and if all are already correct switch to binary search.
            let first_l_to_r = left.iter().position(|l| is_less(r_first, l));
            let last_r_to_l = right.iter().rposition(|r| is_less(r, l_last));

            // This should not be possible to fail, but is_less might be buggy.
            if let (Some(l), Some(r)) = (first_l_to_r, last_r_to_l) {
                // r + 1 because we want an exclusive end bound.
                return Some((l, r + 1));
            }
        }
    }

    None
}

// Given sorted left, right of equal size n it finds smallest i such that
// for all l in left[i..] and r in right[..n-i] we have l > r. By vacuous truth
// n is always a solution (but not necessarily the smallest).
//
// Panics if left, right aren't equal in size or if is_less does.
pub fn crossover_point<T, F: Cmp<T>>(left: &[T], right: &[T], is_less: &mut F) -> usize {
    // Since left and right are sorted we only need to find the smallest i
    // satisfying left[i] > right[n-i-1], or return n if there aren't any,
    // since we'd have l >= left[i] > right[n-i-1] >= r for any l in
    // left[i..] and r in right[..n-i].
    let n = left.len();
    assert!(right.len() == n);

    let mut lo = 0;
    let mut maybe = n;
    // Invariant (1), every position before lo is ruled out.
    // Invariant (2), every position after lo + maybe is ruled out.
    // Invariant (3), lo + maybe <= n.
    // All hold right now, (1) and (2) by vacuous truth.

    // This terminates because each iteration guarantees that
    // new_maybe <= floor(maybe / 2) < maybe.
    while maybe > 0 {
        let step = maybe / 2;
        let i = lo + step;
        let i_valid = unsafe {
            // SAFETY: step < maybe and by invariant (3) we have
            // i = lo + step < lo + maybe <= n, thus i < n. Finally,
            // left.len() == right.len() so n - 1 - i is also in bounds
            is_less(right.get_unchecked(n - 1 - i), left.get_unchecked(i))
        };
        if i_valid {
            // Rule out the positions after i = lo + step as i is valid.
            // Explicitly maintains invariant (2), and (3) since step < maybe.
            // Invariant (1) is unchanged.
            maybe = step;
        } else {
            // Rule out the elements before i = lo + step and i itself.
            // Explicitly maintains invariant (1), invariants (2, 3) are
            // unchanged because lo + maybe doesn't change.
            lo += step + 1;
            maybe -= step + 1;
        }
    }

    // All elements before and after lo have been ruled out, so lo remains.
    lo
}

// Given two sorted slices left, right computes two splitpoints l, r such that
// stably merging (left[..l], right[..r]) followed by (left[l..], right[r..]) is
// equivalent to stably merging (left, right). It is guaranteed that right[..r]
// and left[l..] are of equal size.
//
// Panics if is_less does.
pub fn merge_splitpoints<T, F: Cmp<T>>(left: &[T], right: &[T], is_less: &mut F) -> (usize, usize) {
    let minlen = left.len().min(right.len());
    let left_skip = left.len() - minlen;
    let i = crossover_point(&left[left_skip..], &right[..minlen], is_less);
    (left_skip + i, minlen - i)
}
