use crate::{
    base::Session,
    semantic::analysis::{ObservedTyInferVar, TyCtxt, UnifyCx, UnifyCxMode},
    utils::hash::{FxHashMap, FxHashSet},
};
use index_vec::{IndexVec, define_index_type};
use std::{collections::VecDeque, fmt};

// === Results === //

pub type ObligationResult<T = ()> = Result<T, ObligationNotReady>;

#[derive(Debug, Clone)]
pub struct ObligationNotReady;

// === ObligationCx === //

/// A [`UnifyCx`] extended with the ability to solve obligations out-of-order.
///
/// An obligation is something that must unconditionally hold in order for a program to compile.
/// This means that, unlike `UnifyCx` relations, obligations cannot be tried for success. In return
/// for this strict structure, obligations are automatically scheduled out of order to ensure that
/// all inference variables are solved in the correct order. Additionally, obligations can be solved
/// co-inductively—that is, an obligation can assume itself to be true while proving itself.
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

    /// All obligations ever registered with us.
    all_obligations: IndexVec<ObligationIdx, ObligationState<K>>,

    /// The queue obligations to invoke. These are invoked in FIFO order to ensure that we properly
    /// explore all branches of the proof tree simultaneously.
    run_queue: VecDeque<ObligationIdx>,

    /// A map from inference variables to obligations they could re-run upon being inferred.
    var_wake_ups: FxHashMap<ObservedTyInferVar, Vec<ObligationIdx>>,

    /// The number of observed inference variables we have processed from `ucx`'s
    /// `observed_reveal_order` list.
    rerun_var_read_len: usize,
}

define_index_type! {
    struct ObligationIdx = u32;
}

#[derive(Clone)]
struct ObligationState<K> {
    /// The kind of obligation we're trying to prove.
    kind: K,

    /// The set of variables whose inference could cause us to rerun. Cleared once the obligation is
    /// enqueued to re-run and re-populated if, after the re-run, the obligation is still ambiguous.
    can_wake_by: FxHashSet<ObservedTyInferVar>,
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
            all_obligations: IndexVec::new(),
            run_queue: VecDeque::new(),
            var_wake_ups: FxHashMap::default(),
            rerun_var_read_len: 0,
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
        let idx = self.all_obligations.push(ObligationState {
            kind,
            can_wake_by: FxHashSet::default(),
        });

        self.run_queue.push_back(idx);
    }

    pub fn poll_obligations<T>(
        target: &mut T,
        getter: impl Fn(&mut T) -> &mut Self,
        forker: impl Fn(&T) -> T,
        mut run: impl FnMut(&mut T, K) -> ObligationResult,
    ) {
        loop {
            let this = getter(target);

            // See whether any new obligations can be added to the queue yet.
            for &var in &this.ucx.observed_infer_reveal_order()[this.rerun_var_read_len..] {
                let Some(awoken) = this.var_wake_ups.remove(&var) else {
                    continue;
                };

                for awoken_idx in awoken {
                    let awoken = &mut this.all_obligations[awoken_idx];

                    if !awoken.can_wake_by.contains(&var) {
                        continue;
                    }

                    awoken.can_wake_by.clear();

                    this.run_queue.push_back(awoken_idx);
                }
            }

            this.rerun_var_read_len = this.ucx.observed_infer_reveal_order().len();

            // Obtain the next obligation.
            let Some(curr_idx) = this.run_queue.pop_front() else {
                break;
            };

            let kind = this.all_obligations[curr_idx].kind.clone();

            // Fork the context.
            let mut fork = forker(target);

            // We must trace on the `fork` since stopping the tracing process requires exactly one
            // `UnifyCx` to remain.
            getter(&mut fork).ucx.start_tracing();

            // Process the obligation.
            let res = run(&mut fork, kind);

            // Interpret the result.
            let traced_vars = getter(&mut fork).ucx.finish_tracing();

            match res {
                Ok(()) => {
                    *target = fork;
                }
                Err(ObligationNotReady) => {
                    // Drop the fork to regain access to the `root`.
                    drop(fork);
                    let this = getter(target);

                    // Register wake-ups.
                    let curr = &mut this.all_obligations[curr_idx];

                    for var in traced_vars {
                        if this.ucx.lookup_ty_infer_var(var).is_ok() {
                            continue;
                        }

                        let var = this.ucx.observe_ty_infer_var(var);

                        if !curr.can_wake_by.insert(var) {
                            continue;
                        }

                        this.var_wake_ups.entry(var).or_default().push(curr_idx);
                    }
                }
            }
        }
    }

    pub fn unfulfilled_obligations(&self) -> impl Iterator<Item = &K> {
        self.all_obligations
            .iter()
            .filter(|v| !v.can_wake_by.is_empty())
            .map(|v| &v.kind)
            .chain(
                self.run_queue
                    .iter()
                    .map(|&idx| &self.all_obligations[idx].kind),
            )
    }
}
