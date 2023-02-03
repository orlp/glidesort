#![allow(dead_code)]

use crate::mut_slice::states::Weak;
use crate::mut_slice::MutSlice;

#[derive(Copy, Clone, Debug)]
pub struct Location {
    pub buffer: &'static str,
    pub idx: usize,
}

#[derive(Copy, Clone, Debug)]
pub enum Operation {
    Move { from: Location, to: Location },

    Swap { a: Location, b: Location },

    Compare { lhs: Location, rhs: Location },
}

#[cfg(feature = "tracking")]
mod tracking_impl {
    use std::collections::{HashMap, HashSet};
    use std::sync::Mutex;

    use super::*;

    #[derive(Default)]
    struct TrackingRegister {
        known_buffers: HashMap<&'static str, (usize, usize)>,
        registered_reads: HashSet<usize>,
        registered_writes: HashSet<usize>,
        ops: Vec<Operation>,
    }

    impl TrackingRegister {
        pub fn register_buffer<'l, B, T>(
            &mut self,
            name: &'static str,
            buf: MutSlice<'l, B, T, Weak>,
        ) {
            let old = self
                .known_buffers
                .insert(name, (buf.begin_address(), buf.end_address()));
            assert!(old.is_none(), "duplicate buffer {name}");
        }

        pub fn deregister_buffer(&mut self, name: &'static str) -> (usize, usize) {
            let old = self.known_buffers.remove(name);
            assert!(old.is_some(), "unknown buffer {name}");
            old.unwrap()
        }

        fn locate<T>(&self, ptr: *const T) -> Option<Location> {
            let iptr = ptr as usize;
            for (buf, (begin, end)) in self.known_buffers.iter() {
                if (*begin..*end).contains(&iptr) {
                    return Some(Location {
                        buffer: *buf,
                        idx: (iptr - begin) / std::mem::size_of::<T>(),
                    });
                }
            }
            None
        }
    }

    lazy_static::lazy_static! {
        static ref TRACKING_REGISTER: Mutex<TrackingRegister> = {
            Mutex::new(TrackingRegister::default())
        };
    }

    pub fn read_tracked_ops() -> Vec<Operation> {
        let mut register = TRACKING_REGISTER.lock().unwrap();
        assert!(register.registered_reads.len() == 0);
        assert!(register.registered_writes.len() == 0);
        assert!(register.known_buffers.len() == 0);
        core::mem::take(&mut register.ops)
    }

    pub fn register_buffer<'l, B, T>(name: &'static str, buf: MutSlice<'l, B, T, Weak>) {
        let mut register = TRACKING_REGISTER.lock().unwrap();
        register.register_buffer(name, buf);
    }

    pub fn deregister_buffer(name: &'static str) {
        let mut register = TRACKING_REGISTER.lock().unwrap();
        register.deregister_buffer(name);
    }

    pub fn register_cmp<T>(left: *const T, right: *const T) {
        let mut register = TRACKING_REGISTER.lock().unwrap();
        let lhs = register.locate(left).expect("unregistered cmp lhs");
        let rhs = register.locate(right).expect("unregistered cmp rhs");
        register.ops.push(Operation::Compare { lhs, rhs })
    }

    pub fn track_copy<T>(src: *const T, dst: *mut T, count: usize) {
        if count == 0 {
            return;
        }

        let mut register = TRACKING_REGISTER.lock().unwrap();
        let from = register
            .locate(src)
            .expect("unregistered copy src destination");
        let to = register
            .locate(dst)
            .expect("unregistered copy dst destination");
        if (src..src.wrapping_add(count)).contains(&(dst as *const T)) {
            for i in (0..count).rev() {
                register.ops.push(Operation::Move {
                    from: Location {
                        idx: from.idx + i,
                        buffer: from.buffer,
                    },
                    to: Location {
                        idx: to.idx + i,
                        buffer: to.buffer,
                    },
                });
            }
        } else {
            for i in 0..count {
                register.ops.push(Operation::Move {
                    from: Location {
                        idx: from.idx + i,
                        buffer: from.buffer,
                    },
                    to: Location {
                        idx: to.idx + i,
                        buffer: to.buffer,
                    },
                });
            }
        }
    }

    pub fn track_swap_nonoverlapping<T>(src: *const T, dst: *mut T, count: usize) {
        if count == 0 {
            return;
        }

        let mut register = TRACKING_REGISTER.lock().unwrap();
        let from = register
            .locate(src)
            .expect("unregistered copy src destination");
        let to = register
            .locate(dst)
            .expect("unregistered copy dst destination");
        for i in 0..count {
            register.ops.push(Operation::Swap {
                a: Location {
                    idx: from.idx + i,
                    buffer: from.buffer,
                },
                b: Location {
                    idx: to.idx + i,
                    buffer: to.buffer,
                },
            });
        }
    }
}

/// Dummy implementation.
#[cfg(not(feature = "tracking"))]
#[allow(dead_code)]
mod tracking_impl {
    use super::*;

    #[inline]
    pub fn register_cmp<T>(_left: *const T, _right: *const T) {}
    #[inline]
    pub fn register_buffer<'l, B, T>(_name: &'static str, _sl: MutSlice<'l, B, T, Weak>) {}
    #[inline]
    pub fn deregister_buffer(_name: &'static str) {}
    #[inline]
    pub fn track_copy<T>(_src: *const T, _dst: *mut T, _count: usize) {}
    #[inline]
    pub fn track_swap_nonoverlapping<T>(_a: *const T, _b: *mut T, _count: usize) {}
}

#[cfg(not(feature = "tracking"))]
pub(crate) use core::ptr;

#[cfg(feature = "tracking")]
pub use tracking_impl::read_tracked_ops;
pub(crate) use tracking_impl::{deregister_buffer, register_buffer, register_cmp, track_copy};

#[cfg(feature = "tracking")]
pub(crate) mod ptr {
    use core::ptr as cptr;

    pub use cptr::{read, write};

    #[inline]
    pub unsafe fn swap_nonoverlapping<T>(a: *mut T, b: *mut T, count: usize) {
        super::tracking_impl::track_swap_nonoverlapping(a, b, count);
        unsafe { cptr::swap_nonoverlapping(a, b, count) }
    }

    #[inline]
    pub unsafe fn copy_nonoverlapping<T>(src: *const T, dst: *mut T, count: usize) {
        super::tracking_impl::track_copy(src, dst, count);
        unsafe { cptr::copy_nonoverlapping(src, dst, count) }
    }

    #[inline]
    pub unsafe fn copy<T>(src: *const T, dst: *mut T, count: usize) {
        super::tracking_impl::track_copy(src, dst, count);
        unsafe { cptr::copy(src, dst, count) }
    }
}
