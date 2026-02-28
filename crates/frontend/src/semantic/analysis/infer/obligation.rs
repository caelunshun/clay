use crate::{
    base::Session,
    semantic::analysis::{TyCtxt, UnifyCx, UnifyCxMode},
};
use std::fmt;

// === Results === //

pub type ObligationResult<T = ()> = Result<T, ObligationNotReady>;

#[derive(Debug, Clone)]
pub struct ObligationNotReady;

// === ObligationCx === //

/// A [`UnifyCx`] extended with the ability to solve obligations out-of-order.
///
/// An obligation is something that must unconditionally hold in order for a program to compile.
/// This means that, unlike `UnifyCx` relations, obligations cannot be tried for success. In return
/// for this strict structure, obligations are automatically scheduled out-of-order to ensure that
/// all inference variables are solved in the correct order.
///
/// To push an obligation to an `ObligationCx`, you simply have to call [`push_obligation`].
/// You can then poll these obligations for progress using [`poll_obligations`].
///
/// This context can be forked while processing an obligation but, for efficiency purposes, does not
/// allow forking while not processing obligations.
///
/// [`push_obligation`]: ObligationCx::push_obligation
/// [`poll_obligations`]: ObligationCx::poll_obligations
#[derive(Clone)]
pub struct ObligationCx<'tcx, K> {
    ucx: UnifyCx<'tcx>,
    pending_obligations: Vec<K>,
    made_progress: bool,
}

impl<'tcx, K> fmt::Debug for ObligationCx<'tcx, K> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ObligationCx").finish_non_exhaustive()
    }
}

impl<'tcx, K: Clone> ObligationCx<'tcx, K> {
    pub fn new(tcx: &'tcx TyCtxt, mode: UnifyCxMode) -> Self {
        Self {
            ucx: UnifyCx::new(tcx, mode),
            pending_obligations: Vec::new(),
            made_progress: false,
        }
    }

    pub fn tcx(&self) -> &'tcx TyCtxt {
        self.ucx.tcx()
    }

    pub fn session(&self) -> &'tcx Session {
        self.ucx.session()
    }

    pub fn ucx(&self) -> &UnifyCx<'tcx> {
        &self.ucx
    }

    pub fn ucx_mut(&mut self) -> &mut UnifyCx<'tcx> {
        &mut self.ucx
    }

    pub fn push_obligation(&mut self, kind: K) {
        self.pending_obligations.push(kind);
        self.made_progress = true;
    }

    pub fn poll_obligations<T>(
        target: &mut T,
        getter: impl Fn(&mut T) -> &mut Self,
        forker: impl Fn(&T) -> T,
        mut run: impl FnMut(&mut T, K) -> ObligationResult,
    ) {
        loop {
            let this = getter(target);

            if !this.made_progress {
                break;
            }

            this.made_progress = false;

            // Process all obligations back to front.
            let mut curr_idx = this.pending_obligations.len();

            while curr_idx > 0 {
                curr_idx -= 1;

                let this = getter(target);
                let kind = this.pending_obligations[curr_idx].clone();
                let mut fork = forker(target);

                // Process the obligation.
                let res = run(&mut fork, kind);

                // If we finished processing the obligation, remove it from the queue and mark
                // progress so we can continue processing.
                if res.is_ok() {
                    *target = fork;

                    let this = getter(target);
                    this.pending_obligations.swap_remove(curr_idx);
                    this.made_progress = true;
                }
            }
        }
    }

    pub fn pending_obligations(&self) -> &[K] {
        &self.pending_obligations
    }
}
