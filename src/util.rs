use core::mem::MaybeUninit;

/// Trait alias for comparison functions.
pub trait Cmp<T>: FnMut(&T, &T) -> bool {}
impl<T, F: FnMut(&T, &T) -> bool> Cmp<T> for F {}

/// Helper function for the compiler to infer a closure as Cmp<T>.
#[inline]
pub fn cmp_from_closure<T, F>(f: F) -> F
where
    F: FnMut(&T, &T) -> bool,
{
    f
}

#[inline]
pub fn select<T>(cond: bool, if_true: *mut T, if_false: *mut T) -> *mut T {
    // let mut ret = if_false;
    // unsafe {
    //     core::arch::asm! {
    //         "test {cond}, {cond}",
    //         "cmovnz {ret}, {if_true}",
    //         cond = in(reg) (cond as usize),
    //         if_true = in(reg) if_true,
    //         ret = inlateout(reg) ret,
    //         options(pure, nomem, nostack)
    //     };
    // }
    // ret

    // let mut res = if_false as usize;
    // cmov::cmovnz(cond as usize, if_true as usize, &mut res);
    // res as *mut T

    // let ab = [if_false, if_true];
    // ab[cond as usize]

    // let tpi = if_true as usize;
    // let fpi = if_false as usize;

    // let xor = tpi ^ fpi;
    // let cond_mask = (-(cond as isize)) as usize;
    // let xor_if_true = xor & cond_mask;
    // return (fpi ^ xor_if_true) as *mut T;

    if cond {
        if_true
    } else {
        if_false
    }
}

#[inline]
#[cold]
pub fn abort() -> ! {
    // panic!("abort called");
    #[cfg(not(feature = "unstable"))]
    {
        std::process::abort();
    }
    #[cfg(feature = "unstable")]
    {
        core::intrinsics::abort();
    }
    // unsafe { std::hint::unreachable_unchecked() }
}

#[inline(always)]
pub fn assert_abort(b: bool) {
    if !b {
        abort();
    }
}

pub trait UnwrapAbort {
    type Inner;
    fn unwrap_abort(self) -> Self::Inner;
}

impl<T> UnwrapAbort for Option<T> {
    type Inner = T;

    #[inline]
    fn unwrap_abort(self) -> Self::Inner {
        if let Some(inner) = self {
            inner
        } else {
            abort()
        }
    }
}

impl<T, E> UnwrapAbort for Result<T, E> {
    type Inner = T;

    #[inline]
    fn unwrap_abort(self) -> Self::Inner {
        if let Ok(inner) = self {
            inner
        } else {
            abort()
        }
    }
}

// split_at_spare_mut not stabilized yet.
#[inline]
pub fn split_at_spare_mut<T>(v: &mut Vec<T>) -> (&mut [T], &mut [MaybeUninit<T>]) {
    unsafe {
        let ptr = v.as_mut_ptr();
        let len = v.len();
        let spare_ptr = ptr.add(len);
        let spare_len = v.capacity() - len;

        // SAFETY: the two slices are non-overlapping, and both match their
        // initialization requirements.
        (
            core::slice::from_raw_parts_mut(ptr, len),
            core::slice::from_raw_parts_mut(spare_ptr.cast::<MaybeUninit<T>>(), spare_len),
        )
    }
}


pub unsafe trait IsCopyType {
    fn is_copy_type() -> bool;
}

#[cfg(not(feature = "unstable"))]
unsafe impl<T> IsCopyType for T {
    fn is_copy_type() -> bool { false }
}

#[cfg(feature = "unstable")]
unsafe impl<T> IsCopyType for T {
    default fn is_copy_type() -> bool { false }
}

#[cfg(feature = "unstable")]
unsafe impl<T: Copy> IsCopyType for T {
    fn is_copy_type() -> bool { true }
}


pub unsafe trait MayCallOrdOnCopy {
    fn may_call_ord_on_copy() -> bool;
}

#[cfg(not(feature = "unstable"))]
unsafe impl<T> MayCallOrdOnCopy for T {
    fn may_call_ord_on_copy() -> bool { false }
}

#[cfg(feature = "unstable")]
unsafe impl<T> MayCallOrdOnCopy for T {
    default fn may_call_ord_on_copy() -> bool { false }
}

#[cfg(feature = "unstable")]
#[marker] unsafe trait SafeToCall { }

#[cfg(feature = "unstable")]
unsafe impl<T: SafeToCall> MayCallOrdOnCopy for T {
    fn may_call_ord_on_copy() -> bool { true }
}

#[cfg(feature = "unstable")]
unsafe impl<T: Copy> SafeToCall for T { }

#[cfg(feature = "unstable")]
unsafe impl<T: SafeToCall> SafeToCall for (T, ) { }

#[cfg(feature = "unstable")]
unsafe impl<T: SafeToCall, U: SafeToCall> SafeToCall for (T, U) { }

#[cfg(feature = "unstable")]
unsafe impl<T: SafeToCall, U: SafeToCall, V: SafeToCall> SafeToCall for (T, U, V) { }

macro_rules! impl_safetocallord {
    ($($t:ty, )*) => {
        $(
        #[cfg(feature = "unstable")]
        unsafe impl SafeToCall for $t { }
        )*
    };
}

impl_safetocallord!(String,);