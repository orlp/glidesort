use crate::mut_slice::states::{Init, Uninit, Weak};
use crate::mut_slice::{Brand, MutSlice};
use crate::tracking::ptr;
use crate::util::*;

/// A struct that makes sure the gap is always filled.
pub struct GapGuard<'data, 'gap, DataB, GapB, T> {
    data: MutSlice<'data, DataB, T, Weak>,
    gap: MutSlice<'gap, GapB, T, Weak>,
}

impl<'data, 'gap, DataB: Brand, GapB: Brand, T> GapGuard<'data, 'gap, DataB, GapB, T> {
    pub fn new_disjoint(
        data: MutSlice<'data, DataB, T, Init>,
        gap: MutSlice<'gap, GapB, T, Uninit>,
    ) -> Self {
        unsafe { Self::new_unchecked(data.weak(), gap.weak()) }
    }

    /// SAFETY: it is the caller's responsibility to make sure that when any
    /// method other than len, split_at, concat, data_weak or gap_weak is called,
    /// or when this struct is dropped, that data is Init.
    pub unsafe fn new_unchecked(
        data: MutSlice<'data, DataB, T, Weak>,
        gap: MutSlice<'gap, GapB, T, Weak>,
    ) -> Self {
        if data.len() != gap.len() {
            abort();
        }

        Self { data, gap }
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn data_weak(&self) -> MutSlice<'data, DataB, T, Weak> {
        self.data.weak()
    }

    pub fn gap_weak(&self) -> MutSlice<'gap, GapB, T, Weak> {
        self.gap.weak()
    }

    pub fn split_at(self, i: usize) -> Option<(Self, Self)> {
        unsafe {
            let (data, gap) = self.take_disjoint();
            if let Some((dl, dr)) = data.split_at(i) {
                let (gl, gr) = gap.split_at(i).unwrap_abort();
                Some((
                    GapGuard::new_disjoint(dl, gl),
                    GapGuard::new_disjoint(dr, gr),
                ))
            } else {
                None
            }
        }
    }

    pub fn take_data(self) -> MutSlice<'data, DataB, T, Init> {
        unsafe {
            let data = self.data.weak();
            core::mem::forget(self);
            data.upgrade().assume_init()
        }
    }

    pub fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe {
            let begin = self.data.begin();
            core::slice::from_raw_parts_mut(begin, self.data.len())
        }
    }

    /// Borrows the gap slice.
    ///
    /// SAFETY: the gap must be disjoint from the data.
    pub unsafe fn borrow_gap<'a>(&'a mut self) -> MutSlice<'a, GapB, T, Uninit> {
        unsafe { self.gap.clone().upgrade().assume_uninit() }
    }

    /// SAFETY: it is now the callers responsibility to make sure the gap is
    /// always filled. The data and gap slices must be disjoint.
    pub unsafe fn take_disjoint(
        self,
    ) -> (
        MutSlice<'data, DataB, T, Init>,
        MutSlice<'gap, GapB, T, Uninit>,
    ) {
        unsafe {
            let data = self.data.weak();
            let gap = self.gap.weak();
            core::mem::forget(self);
            (data.upgrade().assume_init(), gap.upgrade().assume_uninit())
        }
    }
}

impl<'gap, 'data, GapB, DataB, T> Drop for GapGuard<'gap, 'data, GapB, DataB, T> {
    #[inline(never)]
    #[cold]
    fn drop(&mut self) {
        unsafe {
            let data_ptr = self.data.begin();
            let gap_ptr = self.gap.begin();
            ptr::copy(data_ptr, gap_ptr, self.data.len());
        }
    }
}
