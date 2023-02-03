use crate::mut_slice::states::AlwaysInit;
use crate::mut_slice::MutSlice;
use crate::util::*;

/// Selects a pivot from left, right.
#[inline]
pub fn select_pivot<'l, 'r, BL, BR, T, F: Cmp<T>>(
    left: MutSlice<'l, BL, T, AlwaysInit>,
    right: MutSlice<'l, BR, T, AlwaysInit>,
    is_less: &mut F,
) -> *mut T {
    unsafe {
        // We use unsafe code and raw pointers here because we're dealing with
        // two non-contiguous buffers and heavy recursion. Passing safe slices
        // around would involve a lot of branches and function call overhead.
        let left = left.raw();
        let right = right.raw();

        // Get a, b, c as the start of three regions of size n / 8, avoiding the
        // boundary in the elements.
        let n = left.len() + right.len();
        let a = if left.len() >= n / 8 {
            left.begin()
        } else {
            right.begin()
        };
        let b = if left.len() >= n / 2 {
            left.begin().add(n / 2).sub(n / 8)
        } else {
            right.end().sub(n / 2)
        };
        let c = if right.len() >= n / 8 {
            right.end().sub(n / 8)
        } else {
            left.end().sub(n / 8)
        };

        if n < crate::PSEUDO_MEDIAN_REC_THRESHOLD {
            median3(a, b, c, is_less)
        } else {
            median3_rec(a, b, c, n / 8, is_less)
        }
    }
}

/// Calculates an approximate median of 3 elements from sections a, b, c, or recursively from an
/// approximation of each, if they're large enough. By dividing the size of each section by 8 when
/// recursing we have logarithmic recursion depth and overall sample from
/// f(n) = 3*f(n/8) -> f(n) = O(n^(log(3)/log(8))) ~= O(n^0.528) elements.
///
/// SAFETY: a, b, c must point to the start of initialized regions of memory of
/// at least n elements.
#[cold]
pub unsafe fn median3_rec<T, F: Cmp<T>>(
    mut a: *mut T,
    mut b: *mut T,
    mut c: *mut T,
    n: usize,
    is_less: &mut F,
) -> *mut T {
    unsafe {
        if n * 8 >= crate::PSEUDO_MEDIAN_REC_THRESHOLD {
            let n8 = n / 8;
            a = median3_rec(a, a.add(n8 * 4), a.add(n8 * 7), n8, is_less);
            b = median3_rec(b, b.add(n8 * 4), b.add(n8 * 7), n8, is_less);
            c = median3_rec(c, c.add(n8 * 4), c.add(n8 * 7), n8, is_less);
        }
        median3(a, b, c, is_less)
    }
}

/// Calculates the median of 3 elements.
///
/// SAFETY: a, b, c must be valid initialized elements.
#[inline(always)]
unsafe fn median3<T, F: Cmp<T>>(a: *mut T, b: *mut T, c: *mut T, is_less: &mut F) -> *mut T {
    // Compiler tends to make this branchless when sensible, and avoids the
    // third comparison when not.
    unsafe {
        let x = is_less(&*a, &*b);
        let y = is_less(&*a, &*c);
        if x == y {
            // If x=y=0 then b, c <= a. In this case we want to return max(b, c).
            // If x=y=1 then a < b, c. In this case we want to return min(b, c).
            // By toggling the outcome of b < c using XOR x we get this behavior.
            let z = is_less(&*b, &*c);
            select(z ^ x, c, b)
        } else {
            // Either c <= a < b or b <= a < c, thus a is our median.
            a
        }
    }
}
