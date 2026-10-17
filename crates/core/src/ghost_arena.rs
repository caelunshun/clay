use bumpalo::Bump;
use derive_where::derive_where;
use std::{
    marker::PhantomData,
    num::NonZeroU64,
    ptr::{self, NonNull},
    sync::atomic::{AtomicU64, Ordering::*},
};

pub struct GhostArena {
    bump: Bump,
    uid: NonZeroU64,
}

impl Default for GhostArena {
    fn default() -> Self {
        static UID_GEN: AtomicU64 = AtomicU64::new(1);

        Self {
            bump: Default::default(),
            uid: NonZeroU64::new(UID_GEN.fetch_add(1, Relaxed)).unwrap(),
        }
    }
}

impl GhostArena {
    pub fn acquire_mut<R>(
        &mut self,
        f: impl for<'g> FnOnce(&mut GhostArenaAcquired<'g>) -> R,
    ) -> R {
        f(unsafe { &mut *(self as *mut GhostArena as *mut GhostArenaAcquired<'_>) })
    }

    pub fn acquire_ref<R>(&self, f: impl for<'g> FnOnce(&GhostArenaAcquired<'g>) -> R) -> R {
        f(unsafe { &*(self as *const GhostArena as *const GhostArenaAcquired<'_>) })
    }
}

#[repr(transparent)]
pub struct GhostArenaAcquired<'g> {
    _marker: PhantomData<fn(&'g ()) -> &'g ()>,
    arena: GhostArena,
}

#[derive_where(Copy, Clone)]
pub struct GhostPtr<'g, T: ?Sized + GhostPointee<'g>> {
    _marker: PhantomData<fn(&'g ()) -> &'g ()>,
    ptr: NonNull<T>,
}

impl<'g, T: ?Sized + GhostPointee<'g>> GhostPtr<'g, T> {
    pub fn new(value: T, ar: &GhostArenaAcquired<'g>) -> Self
    where
        T: Sized,
    {
        Self {
            _marker: PhantomData,
            ptr: NonNull::from(ar.arena.bump.alloc(value)),
        }
    }

    pub fn r<'a>(self, ar: &'a GhostArenaAcquired<'g>) -> &'a T {
        _ = ar;
        unsafe { self.ptr.as_ref() }
    }

    pub fn m<'a>(mut self, ar: &'a mut GhostArenaAcquired<'g>) -> &'a mut T {
        _ = ar;
        unsafe { self.ptr.as_mut() }
    }

    pub fn liberate(self, ar: &GhostArenaAcquired<'g>) -> DynGhostPtr<T::ForLt<'static>> {
        DynGhostPtr {
            uid: ar.arena.uid,
            ptr: recast_ptr(self.ptr),
        }
    }
}

pub unsafe trait GhostPointee<'g> {
    type ForLt<'new_g>: ?Sized
        + for<'possible_g> GhostPointee<'new_g, ForLt<'possible_g> = Self::ForLt<'possible_g>>;
}

fn recast_ptr<'a, 'b, T>(ptr: NonNull<T>) -> NonNull<T::ForLt<'b>>
where
    T: ?Sized + GhostPointee<'a>,
{
    unsafe { ptr::read(&ptr as *const NonNull<T> as *const NonNull<_>) }
}

#[derive_where(Copy, Clone)]
pub struct DynGhostPtr<T: ?Sized + GhostPointee<'static>> {
    uid: NonZeroU64,
    ptr: NonNull<T>,
}

impl<T: ?Sized + GhostPointee<'static>> DynGhostPtr<T> {
    pub fn rejoin<'g>(self, ar: &GhostArenaAcquired<'g>) -> GhostPtr<'g, T::ForLt<'g>> {
        assert_eq!(self.uid, ar.arena.uid);

        GhostPtr {
            _marker: PhantomData,
            ptr: recast_ptr(self.ptr),
        }
    }
}
