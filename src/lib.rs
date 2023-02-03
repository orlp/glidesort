#![deny(unsafe_op_in_unsafe_fn)]
#![cfg_attr(feature = "unstable", feature(core_intrinsics))]
#![cfg_attr(feature = "unstable", allow(incomplete_features))]
#![cfg_attr(feature = "unstable", feature(specialization, marker_trait_attr))]

//! Glidesort is a novel stable sorting algorithm that combines the best-case behavior of
//! Timsort-style merge sorts for pre-sorted data with the best-case behavior of pattern-defeating
//! quicksort for data with many duplicates. It is a comparison-based sort supporting arbitrary
//! comparison operators, and while exceptional on data with patterns it is also very fast for
//! random data.
//! 
//! For more information see the [readme](https://github.com/orlp/glidesort).

// We avoid a dynamic allocation for our scratch buffer if a scratch buffer of
// this size is sufficient and the user did not provide one.
const MAX_STACK_SCRATCH_SIZE_BYTES: usize = 4096;

// When sorting N elements we allocate a buffer of at most size N, N/2 or N/8
// depending on how large the data is.
const FULL_ALLOC_MAX_BYTES: usize = 1024 * 1024;
const HALF_ALLOC_MAX_BYTES: usize = 1024 * 1024 * 1024;

// If the total size of a merge operation is above this threshold glidesort will
// attempt to split it into (instruction-level) parallel merges when applicable.
const MERGE_SPLIT_THRESHOLD: usize = 32;

// Recursively select a pseudomedian if above this threshold.
const PSEUDO_MEDIAN_REC_THRESHOLD: usize = 64;

// For this many or fewer elements we switch to our small sorting algorithm.
const SMALL_SORT: usize = 48;

// We always need the tracking module internally to provide a fallback dummy
// implementation to prevent adding conditional compilation everywhere.
#[cfg(not(feature = "tracking"))]
mod tracking;
#[cfg(feature = "tracking")]
pub mod tracking;

mod branchless_merge;
mod gap_guard;
mod glidesort;
mod merge_reduction;
mod mut_slice;
mod physical_merges;
mod pivot_selection;
mod powersort;
mod small_sort;
mod stable_quicksort;
mod util;

use core::cmp::Ordering;
use core::mem::{ManuallyDrop, MaybeUninit};

use util::*;

use crate::mut_slice::states::AlwaysInit;
use crate::mut_slice::{Brand, MutSlice};

fn glidesort_alloc_size<T>(n: usize) -> usize {
    let tlen = core::mem::size_of::<T>();
    let full_allowed = n.min(FULL_ALLOC_MAX_BYTES / tlen);
    let half_allowed = (n / 2).min(HALF_ALLOC_MAX_BYTES / tlen);
    let eighth_allowed = n / 8;
    full_allowed.max(half_allowed).max(eighth_allowed)
}

/// See [`slice::sort`].
pub fn sort<T: Ord>(v: &mut [T]) {
    sort_by(v, |a, b| a.cmp(b))
}

/// See [`slice::sort_by_key`].
pub fn sort_by_key<T, F: FnMut(&T) -> K, K: Ord>(v: &mut [T], mut f: F) {
    sort_by(v, |a, b| f(a).cmp(&f(b)))
}

/// See [`slice::sort_by`].
pub fn sort_by<T, F>(v: &mut [T], mut compare: F)
where
    F: FnMut(&T, &T) -> Ordering,
{
    // Zero-sized types are either always or never sorted, as they can not carry
    // any information that would allow the permutation to change.
    if core::mem::size_of::<T>() == 0 {
        return;
    }

    let mut is_less = cmp_from_closure(|a, b| {
        tracking::register_cmp(a, b);
        compare(a, b) == Ordering::Less
    });

    let n = v.len();
    MutSlice::from_mut_slice(v, |el| {
        // Fast path for very small arrays.
        if n < SMALL_SORT {
            return small_sort::small_sort(el, &mut is_less);
        }

        // Avoid dynamic allocation if possible.
        let stack_buffer_cap = MAX_STACK_SCRATCH_SIZE_BYTES / core::mem::size_of::<T>();
        if stack_buffer_cap >= n / 2 {
            return glidesort_with_max_stack_scratch(el, &mut is_less);
        }

        let mut scratch_alloc = Vec::new();
        let (_, buffer) = make_scratch_after_vec(&mut scratch_alloc, glidesort_alloc_size::<T>(n));
        MutSlice::from_maybeuninit_mut_slice(buffer, |scratch| {
            glidesort::glidesort(el, scratch.assume_uninit(), &mut is_less, false)
        })
    })
}

/// Like [`sort`], except this function does not allocate and uses the passed buffer instead.
pub fn sort_with_buffer<T: Ord>(v: &mut [T], buffer: &mut [MaybeUninit<T>]) {
    sort_with_buffer_by(v, buffer, |a, b| a.cmp(b))
}

/// Like [`sort_by_key`], except this function does not allocate and uses the passed buffer instead.
pub fn sort_with_buffer_by_key<T, F: FnMut(&T) -> K, K: Ord>(
    v: &mut [T],
    buffer: &mut [MaybeUninit<T>],
    mut f: F,
) {
    sort_with_buffer_by(v, buffer, |a, b| f(a).cmp(&f(b)))
}

/// Like [`sort_by`], except this function does not allocate and uses the passed buffer instead.
pub fn sort_with_buffer_by<T, F>(v: &mut [T], buffer: &mut [MaybeUninit<T>], mut compare: F)
where
    F: FnMut(&T, &T) -> Ordering,
{
    // Zero-sized types are either always or never sorted, as they can not carry
    // any information that would allow the permutation to change.
    if core::mem::size_of::<T>() == 0 {
        return;
    }

    let mut is_less = cmp_from_closure(|a, b| {
        tracking::register_cmp(a, b);
        compare(a, b) == Ordering::Less
    });

    let n = v.len();
    MutSlice::from_mut_slice(v, |el| {
        // Fast path for very small arrays.
        if n < SMALL_SORT {
            return small_sort::small_sort(el, &mut is_less);
        }

        MutSlice::from_maybeuninit_mut_slice(buffer, |scratch| {
            glidesort::glidesort(el, scratch.assume_uninit(), &mut is_less, false)
        })
    })
}

/// Like [`sort`], except this function allocates its space at the end of the given `Vec`.
pub fn sort_in_vec<T: Ord>(v: &mut Vec<T>) {
    sort_in_vec_by(v, |a, b| a.cmp(b))
}

/// Like [`sort_by_key`], except this function allocates its space at the end of the given `Vec`.
pub fn sort_in_vec_by_key<T, F: FnMut(&T) -> K, K: Ord>(v: &mut Vec<T>, mut f: F) {
    sort_in_vec_by(v, |a, b| f(a).cmp(&f(b)))
}

/// Like [`sort_by`], except this function allocates its space at the end of the given `Vec`.
pub fn sort_in_vec_by<T, F>(v: &mut Vec<T>, mut compare: F)
where
    F: FnMut(&T, &T) -> Ordering,
{
    // Zero-sized types are either always or never sorted, as they can not carry
    // any information that would allow the permutation to change.
    if core::mem::size_of::<T>() == 0 {
        return;
    }

    let mut is_less = cmp_from_closure(|a, b| {
        tracking::register_cmp(a, b);
        compare(a, b) == Ordering::Less
    });

    let n = v.len();
    // Fast path for very small arrays.
    if n < SMALL_SORT {
        return MutSlice::from_mut_slice(v, |el| small_sort::small_sort(el, &mut is_less));
    }

    // Avoid dynamic allocation if possible.
    let stack_buffer_cap = MAX_STACK_SCRATCH_SIZE_BYTES / core::mem::size_of::<T>();
    if stack_buffer_cap >= n / 2 {
        return MutSlice::from_mut_slice(v, |el| {
            glidesort_with_max_stack_scratch(el, &mut is_less)
        });
    }

    let (el, buffer) = make_scratch_after_vec(v, glidesort_alloc_size::<T>(n));
    MutSlice::from_mut_slice(el, |el| {
        MutSlice::from_maybeuninit_mut_slice(buffer, |scratch| {
            glidesort::glidesort(el, scratch.assume_uninit(), &mut is_less, false)
        })
    })
}

/// Make and return scratch space after the elements of a Vec.
fn make_scratch_after_vec<T>(
    buffer: &mut Vec<T>,
    mut target_size: usize,
) -> (&mut [T], &mut [MaybeUninit<T>]) {
    // Avoid reallocation if reasonable.
    let free_capacity = buffer.capacity() - buffer.len();
    if free_capacity / 2 < target_size {
        while let Err(_) = buffer.try_reserve(target_size) {
            // We are in a low-memory situation, we'd much prefer a bit slower sorting
            // over completely running out, so aggressively reduce our memory request.
            target_size /= 8;
            if target_size == 0 {
                return (&mut buffer[..], &mut []);
            }
        }
    }

    split_at_spare_mut(buffer)
}

// We really don't want to inline this in order to prevent always taking up
// extra stack space in non-taken branches, mainly for embedded devices.
// A buffer of N bytes aligned as T would be.
#[repr(C)]
union AlignedBuffer<T, const N: usize> {
    buffer: [MaybeUninit<u8>; N],
    _dummy_for_alignment: ManuallyDrop<MaybeUninit<T>>,
}

#[inline(never)]
#[cold]
fn glidesort_with_max_stack_scratch<'l, B: Brand, T, F: Cmp<T>>(
    el: MutSlice<'l, B, T, AlwaysInit>,
    is_less: &mut F,
) {
    unsafe {
        // SAFETY: we assume a [MaybeUninit<u8>; N] is initialized, which it
        // trivially is as it makes no guarantees.
        let mut aligned_buffer: AlignedBuffer<T, MAX_STACK_SCRATCH_SIZE_BYTES> =
            MaybeUninit::uninit().assume_init();
        let aligned_buffer_bytes = aligned_buffer.buffer.as_mut_slice();

        // SAFETY: our buffer is aligned and we can fit this many elements.
        let max_elements = MAX_STACK_SCRATCH_SIZE_BYTES / core::mem::size_of::<T>();
        let buffer = core::slice::from_raw_parts_mut(
            aligned_buffer_bytes.as_mut_ptr().cast::<MaybeUninit<T>>(),
            max_elements,
        );

        MutSlice::from_maybeuninit_mut_slice(buffer, |scratch| {
            glidesort::glidesort(el, scratch.assume_uninit(), is_less, false)
        })
    }
}
