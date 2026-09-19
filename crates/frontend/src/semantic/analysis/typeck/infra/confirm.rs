use crate::{
    semantic::analysis::typeck::BodyCtxt,
    utils::mem::{GpAnyMutPtr, GpErasedMutPtr, GpMutPtr},
};
use derive_where::derive_where;
use std::mem;

#[derive_where(Debug, Copy, Clone)]
pub struct ConfirmExpr<'a, 'tcx, T> {
    cb: GpErasedMutPtr<dyn 'a + ConfirmExprHandle<'a, 'tcx, Confirmed = T>>,
}

impl<'a, 'tcx, T> ConfirmExpr<'a, 'tcx, T> {
    pub fn new<F>(f: F, bcx: &BodyCtxt<'a, 'tcx>) -> Self
    where
        F: 'a + FnOnce(&mut BodyCtxt<'a, 'tcx>) -> T,
        T: 'a + Clone,
    {
        enum State<T, F> {
            Resolved(T),
            Unresolved(F),
            Solving,
        }

        impl<'a, 'tcx, T, F> ConfirmExprHandle<'a, 'tcx> for GpMutPtr<State<T, F>>
        where
            F: FnOnce(&mut BodyCtxt<'a, 'tcx>) -> T,
            T: Clone,
        {
            type Confirmed = T;

            fn confirm(&self, bcx: &mut BodyCtxt<'a, 'tcx>) -> Self::Confirmed {
                match self.r(&bcx.confirm_arena) {
                    State::Unresolved(_) => {
                        let State::Unresolved(f) =
                            mem::replace(self.m(&mut bcx.confirm_arena), State::Solving)
                        else {
                            unreachable!()
                        };

                        let solved = f(bcx);
                        *self.m(&mut bcx.confirm_arena) = State::Resolved(solved.clone());
                        solved
                    }
                    State::Resolved(v) => v.clone(),
                    State::Solving => unreachable!("recursive confirmation"),
                }
            }
        }

        let cb = GpMutPtr::new(State::<T, F>::Unresolved(f), &bcx.confirm_arena)
            .erase(|v| v as &(dyn 'a + ConfirmExprHandle<Confirmed = T>));

        Self { cb }
    }

    pub fn confirm(&mut self, bcx: &mut BodyCtxt<'a, 'tcx>) -> T {
        self.cb.confirm(bcx)
    }
}

trait ConfirmExprHandle<'a, 'tcx>: GpAnyMutPtr {
    type Confirmed;

    fn confirm(&self, bcx: &mut BodyCtxt<'a, 'tcx>) -> Self::Confirmed;
}
