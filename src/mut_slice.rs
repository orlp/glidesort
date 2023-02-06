#![allow(dead_code)]

use core::marker::PhantomData;
use core::mem::MaybeUninit;

use crate::tracking::{self, ptr};
use crate::util::abort;

// Branding.
// See GhostCell: https://plv.mpi-sws.org/rustbelt/ghostcell/.
pub struct InvariantLifetime<'id>(PhantomData<*mut &'id ()>);
pub struct Unbranded;

pub trait Brand {}
impl<'id> Brand for InvariantLifetime<'id> {}

// States.
#[rustfmt::skip]
#[allow(clippy::missing_safety_doc)]
pub mod states {
    pub struct Weak;
    pub struct Uninit;
    pub struct MaybeInit;
    pub struct Init;
    pub struct AlwaysInit;

    pub unsafe trait State { type Borrowed; }
    unsafe impl State for Weak { type Borrowed = Weak; }
    unsafe impl State for Uninit { type Borrowed = Uninit; }
    unsafe impl State for MaybeInit { type Borrowed = MaybeInit; }
    unsafe impl State for Init { type Borrowed = AlwaysInit; } // Borrow may not invalidate Init.
    unsafe impl State for AlwaysInit { type Borrowed = AlwaysInit; }

    pub unsafe trait RawAccess {}
    unsafe impl RawAccess for Uninit {}
    unsafe impl RawAccess for MaybeInit {}
    unsafe impl RawAccess for Init {}

    pub unsafe trait IsInit {}
    unsafe impl IsInit for Init {}
    unsafe impl IsInit for AlwaysInit {}
}

use states::*;

/// A more flexible mutable slice for dealing with splitting/concatenation
/// better in a safe way, and tracking initialization state. Without this
/// type-level safety programming almost all of Glidesort would have to be
/// unsafe using raw pointers. NOTE: MutSlice is not to be used with zero-sized
/// types.
///
/// There are two extra aspects to a MutSlice (other than lifetime 'l and type T):
///
/// - Branding B. Each MutSlice is either branded or unbranded. If a MutSlice is
///   branded we know for certain that it is uniquely associated with some
///   allocation that its pointers have full provenance over, so we can safely
///   concatenate slices with the same brand.
///
/// - State S. Used to track the state of this slice.
///
///     1. Weak, in this state the slice contents may not be accessed through
///        this slice object, but using it a location can be kept around for
///        bookkeeping purposes. A weak slice can be upgraded to the other
///        states, albeit unsafely, as it could create aliasing mutable slices.
///     2. Uninit, stating this slice *currently* has no initialized values.
///        This is a very weak guarantee since violating it simply instantly
///        leaks values. It is mainly intended as a hint.
///     3. MaybeInit, making no guarantees, like &mut [MaybeUninit<T>]. To
///        prevent confusion with that type we chose this name.
///     4. Init, stating this slice *currently* only has initialized values.
///     5. AlwaysInit, like Init but the region of memory this slice points to
///        must *always* be restored to be fully initialized regardless of what
///        happens, even if something panics. This is similar to &mut [T].
///        Getting out of this state is always unsafe for this reason.
///
///   Other than the weak state all states imply disjointness with all other
///   slices.
pub struct MutSlice<'l, B, T, S> {
    begin: *mut T,
    end: *mut T,
    _lifetime: PhantomData<&'l mut T>,
    _metadata: PhantomData<(B, S)>,
}

unsafe impl<'l, B, T, S> Send for MutSlice<'l, B, T, S> {}

impl<'l, B, T, S> core::fmt::Debug for MutSlice<'l, B, T, S> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("MutSlice")
            .field("begin", &self.begin)
            .field("end", &self.end)
            .finish()
    }
}

// The only ways to create a new branded slice.
impl<'l, 'b, T> MutSlice<'l, InvariantLifetime<'b>, T, AlwaysInit> {
    #[inline]
    pub fn from_mut_slice<R>(
        sl: &'l mut [T],
        f: impl for<'b2> FnOnce(MutSlice<'l, InvariantLifetime<'b2>, T, AlwaysInit>) -> R,
    ) -> R {
        let len = sl.len();
        let ptr = sl.as_mut_ptr();
        f(unsafe {
            // SAFETY: we create a new unique distinct brand through phantom
            // lifetime 'b2 for this allocation, and we respect &mut [T]'s
            // AlwaysInit property.
            MutSlice::from_pair_unchecked(ptr, ptr.add(len))
        })
    }
}

impl<'l, 'b, T> MutSlice<'l, InvariantLifetime<'b>, T, MaybeInit> {
    #[inline]
    pub fn from_maybeuninit_mut_slice<R>(
        sl: &'l mut [MaybeUninit<T>],
        f: impl for<'b2> FnOnce(MutSlice<'l, InvariantLifetime<'b2>, T, MaybeInit>) -> R,
    ) -> R {
        let len = sl.len();
        let ptr = sl.as_mut_ptr() as *mut T;
        f(unsafe {
            // SAFETY: we create a new unique distinct brand through phantom
            // lifetime 'b2 for this allocation.
            MutSlice::from_pair_unchecked(ptr, ptr.add(len))
        })
    }
}

impl<'l, B, T, S> MutSlice<'l, B, T, S> {
    // Basics.
    #[inline]
    pub unsafe fn from_pair_unchecked(begin: *mut T, end: *mut T) -> Self {
        // SAFETY: up to the caller to check.
        Self {
            begin,
            end,
            _lifetime: PhantomData,
            _metadata: PhantomData,
        }
    }

    #[inline]
    pub unsafe fn transmute_metadata<B2, S2>(self) -> MutSlice<'l, B2, T, S2> {
        // SAFETY: up to the caller to check.
        unsafe { MutSlice::from_pair_unchecked(self.begin, self.end) }
    }

    #[inline]
    pub fn len(&self) -> usize {
        // SAFETY: okay per our type invariant.
        unsafe { self.end.offset_from(self.begin) as usize }
    }

    #[inline]
    pub fn contains(&self, ptr: *mut T) -> bool {
        (self.begin..self.end).contains(&ptr)
    }

    /// Splits this slice into slice[..i] and slice[i..].
    /// Returns None if i > self.len().
    #[inline]
    pub fn split_at(self, i: usize) -> Option<(Self, Self)> {
        unsafe {
            if i <= self.len() {
                // SAFETY: if check protects us.
                let mid = self.begin.add(i);

                // SAFETY: brand/state is preserved.
                Some((
                    Self::from_pair_unchecked(self.begin, mid),
                    Self::from_pair_unchecked(mid, self.end),
                ))
            } else {
                None
            }
        }
    }

    #[inline]
    pub fn split_at_end(self, i: usize) -> Option<(Self, Self)> {
        self.len().checked_sub(i).and_then(|ni| self.split_at(ni))
    }

    /// Splits off i elements from the begin of this slice into a separate slice.
    #[inline]
    pub fn split_off_begin(&mut self, i: usize) -> Self {
        if i <= self.len() {
            unsafe {
                let mid = self.begin.add(i);
                let other = Self::from_pair_unchecked(self.begin, mid);
                self.begin = mid;
                other
            }
        } else {
            abort()
        }
    }

    /// Splits off i elements from the end of this slice into a separate slice.
    #[inline]
    pub fn split_off_end(&mut self, i: usize) -> Self {
        if i <= self.len() {
            unsafe {
                let mid = self.end.sub(i);
                let other = Self::from_pair_unchecked(mid, self.end);
                self.end = mid;
                other
            }
        } else {
            abort()
        }
    }

    // For debugging without becoming unsafe.
    pub fn begin_address(&self) -> usize {
        self.begin as usize
    }

    pub fn end_address(&self) -> usize {
        self.end as usize
    }
}

// We only implement concat for branded slices.
impl<'l, B: Brand, T, S> MutSlice<'l, B, T, S> {
    /// Concatenates two slices if self and right are contiguous, in that order.
    /// Aborts if they are not.
    #[inline]
    pub fn concat(self, right: Self) -> Self {
        unsafe {
            if self.end == right.begin {
                // SAFETY: the check makes sure this is correct, as the brand on
                // Self guarantees us these two slices point in the same allocation
                // with full provenance. Brand/state is preserved.
                Self::from_pair_unchecked(self.begin, right.end)
            } else {
                abort();
            }
        }
    }
}

// ======== Access/mutation ========
#[rustfmt::skip]
impl<'l, B, T, S> MutSlice<'l, B, T, S> {
    #[inline] pub fn begin(&self) -> *mut T { self.begin }
    #[inline] pub fn end(&self) -> *mut T { self.end }
}

#[rustfmt::skip]
impl<'l, B, T, S> MutSlice<'l, B, T, S> {
    // Unsafe bounds mutation, safety must be maintained by caller.
    #[inline] pub unsafe fn add_begin(&mut self, n: usize) { self.begin = unsafe { self.begin.add(n) } }
    #[inline] pub unsafe fn sub_begin(&mut self, n: usize) { self.begin = unsafe { self.begin.sub(n) } }
    #[inline] pub unsafe fn wrapping_add_begin(&mut self, n: usize) { self.begin = self.begin.wrapping_add(n) }
    #[inline] pub unsafe fn wrapping_sub_begin(&mut self, n: usize) { self.begin = self.begin.wrapping_sub(n) }
    #[inline] pub unsafe fn add_end(&mut self, n: usize) { self.end = unsafe { self.end.add(n) } }
    #[inline] pub unsafe fn sub_end(&mut self, n: usize) { self.end = unsafe { self.end.sub(n) } }
    #[inline] pub unsafe fn wrapping_add_end(&mut self, n: usize) { self.end = self.end.wrapping_add(n) }
    #[inline] pub unsafe fn wrapping_sub_end(&mut self, n: usize) { self.end = self.end.wrapping_sub(n) }
}

impl<'l, B, T> MutSlice<'l, B, T, Init> {
    #[inline]
    pub fn move_to<'dst_l, DstB>(
        self,
        dst: MutSlice<'dst_l, DstB, T, Uninit>,
    ) -> (MutSlice<'l, B, T, Uninit>, MutSlice<'dst_l, DstB, T, Init>) {
        unsafe {
            if self.len() != dst.len() {
                abort();
            }

            // SAFETY: we may write to dst, and this write can be assumed to be
            // non-overlapping by slice disjointness. The lengths are equal.
            ptr::copy_nonoverlapping(self.begin(), dst.begin(), self.len());
            (self.assume_uninit(), dst.assume_init())
        }
    }
}

// ========= Conversions =========
// The *only* way to get rid of AlwaysInit is to raw() it, which is unsafe.
impl<'l, B, T> MutSlice<'l, B, T, AlwaysInit> {
    /// SAFETY: I solemny swear that I will ensure this slice is properly
    /// initialized before returning to whoever gave me the AlwaysInit slice,
    /// even in the case of panics.
    #[inline]
    pub unsafe fn raw(self) -> MutSlice<'l, B, T, Init> {
        unsafe { self.transmute_metadata() }
    }
}

// The other way around is always safe.
impl<'l, B, T> MutSlice<'l, B, T, Init> {
    #[inline]
    pub fn always_init(self) -> MutSlice<'l, B, T, AlwaysInit> {
        // SAFETY: this just adds a guarantee that's currently true.
        unsafe { self.transmute_metadata() }
    }
}

// Shedding/regaining state.
impl<'l, B, T, S> MutSlice<'l, B, T, S> {
    #[inline]
    pub fn forget_brand(self) -> MutSlice<'l, Unbranded, T, S> {
        // SAFETY: a brand only grants permissions, it's always safe to drop it.
        unsafe { self.transmute_metadata() }
    }

    #[inline]
    pub fn weak(&self) -> MutSlice<'l, B, T, Weak> {
        // SAFETY: it's always safe to make a weak slice, even from &self.
        unsafe { MutSlice::from_pair_unchecked(self.begin, self.end) }
    }
}

impl<'l, B, T> MutSlice<'l, B, T, Weak> {
    /// SAFETY: the caller is responsible for ensuring this slice does not alias.
    #[inline]
    pub unsafe fn upgrade(self) -> MutSlice<'l, B, T, MaybeInit> {
        unsafe { self.transmute_metadata() }
    }
}

// Non-AlwaysInit initialization conversions.
impl<'l, B, T, S: RawAccess> MutSlice<'l, B, T, S> {
    /// SAFETY: slice must only contain initialized objects.
    #[inline]
    pub unsafe fn assume_init(self) -> MutSlice<'l, B, T, Init> {
        unsafe { self.transmute_metadata() }
    }

    #[inline]
    pub fn assume_uninit(self) -> MutSlice<'l, B, T, Uninit> {
        // SAFETY: at worst this leaks objects.
        unsafe { self.transmute_metadata() }
    }

    #[inline]
    pub fn allow_maybe_init(self) -> MutSlice<'l, B, T, MaybeInit> {
        // SAFETY: this drops all init guarantees.
        unsafe { self.transmute_metadata() }
    }
}

// ========= Borrows, clones, moves. =========
impl<'l, B, T, S> MutSlice<'l, B, T, S> {
    /// Takes this slice, leaving behind an empty slice.
    #[inline]
    pub fn take(&mut self) -> Self {
        unsafe {
            // SAFETY: we make ourselves the empty slice which is disjoint with
            // any other slice and return a copy of original.
            let weak = self.weak();
            self.sub_end(self.len());
            weak.transmute_metadata()
        }
    }
}

impl<'l, B, T, S: IsInit> MutSlice<'l, B, T, S> {
    #[inline]
    pub fn as_slice<'a>(&'a self) -> &'a [T] {
        // SAFETY: we're disjoint and initialized, so this is fine.
        unsafe { core::slice::from_raw_parts(self.begin, self.len()) }
    }

    #[inline]
    pub fn as_mut_slice<'a>(&'a mut self) -> &'a mut [T] {
        // SAFETY: we're disjoint and initialized, so this is fine.
        unsafe { core::slice::from_raw_parts_mut(self.begin, self.len()) }
    }
}

impl<'l, B, T, S: State> MutSlice<'l, B, T, S> {
    #[inline]
    pub fn borrow<'a>(&'a mut self) -> MutSlice<'a, B, T, S::Borrowed> {
        // SAFETY: Lifetime 'a ensures self can't be used at the same time as
        // the slice we return. The State::Borrowed state ensure that
        // no matter what the borrower does (safely), it can't violate the
        // original state.
        unsafe { MutSlice::from_pair_unchecked(self.begin, self.end) }
    }
}

impl<'l, B, T> Clone for MutSlice<'l, B, T, Weak> {
    #[inline]
    fn clone(&self) -> Self {
        // SAFETY: it's safe to clone a weak slice.
        self.weak()
    }
}

/// Helper function to get scratch space on the stack.
#[inline(always)]
pub fn with_stack_scratch<const N: usize, T, R, F>(name: &'static str, f: F) -> R
where
    F: for<'l, 'b> FnOnce(MutSlice<'l, InvariantLifetime<'b>, T, Uninit>) -> R,
{
    let mut scratch_space: [MaybeUninit<T>; N] = unsafe { MaybeUninit::uninit().assume_init() };
    MutSlice::from_maybeuninit_mut_slice(&mut scratch_space, |scratch| {
        tracking::register_buffer(name, scratch.weak());
        let ret = f(scratch.assume_uninit());
        tracking::deregister_buffer(name);
        ret
    })
}
