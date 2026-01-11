use crate::{
    base::{ErrorGuaranteed, Session},
    semantic::analysis::{ObservedTyInferVar, TyCtxt, UnifyCx, UnifyCxMode},
    utils::hash::{FxHashMap, FxHashSet},
};
use derive_where::derive_where;
use index_vec::{IndexVec, define_index_type};
use std::{cell::Cell, collections::VecDeque, fmt, mem, rc::Rc};

// === Definitions === //

#[derive(Debug, Clone)]
pub enum ObligationResult {
    /// The obligation was successfully satisfied.
    Success,

    /// The obligation is guaranteed to fail.
    Failure(ErrorGuaranteed),

    /// The obligation failed because we're still waiting on one or more of the inference variables
    /// to be specified unambiguously or, in rare cases, because the program is ill-formed in some
    /// other way which introduces an ambiguity (e.g. if trait coherence checks failed).
    ///
    /// If this variant is returned, the obligation will be queued to rerun once one or more
    /// inference variables accessed during the execution of the obligation are revealed.
    NotReady,
}

// === ObligationCx === //

/// A [`UnifyCx`] extended with the ability to solve obligations out-of-order.
///
/// An obligation is something that must unconditionally hold in order for a program to compile.
/// This means that, unlike `UnifyCx` relations, obligations cannot be tried for success. In return
/// for this strict structure, obligations are automatically scheduled out of order to ensure that
/// all inference variables are solved in the correct order. Additionally, obligations can be solved
/// co-inductively—that is, an obligation can assume itself to be true while proving itself.
///
/// To push an obligation to an `ObligationCx`, you simply have to call [`push_obligation_no_poll`].
/// You can then poll these obligations for progress using [`poll_obligations`].
///
/// This context can be forked while processing an obligation but, for efficiency purposes, does not
/// allow forking while not processing obligations.
///
/// [`push_obligation_no_poll`]: ObligationCx::push_obligation_no_poll
/// [`poll_obligations`]: ObligationCx::poll_obligations
#[derive(Clone)]
pub struct ObligationCx<'tcx, K> {
    ucx: UnifyCx<'tcx>,
    root: Rc<ObligationCxRoot<K>>,
    local_obligation_queue: Rc<Vec<QueuedObligation<K>>>,
}

#[derive(Clone)]
struct QueuedObligation<K> {
    parent: Option<ObligationIdx>,
    kind: K,
}

#[derive_where(Default)]
struct ObligationCxRoot<K> {
    eval_suppressed: Cell<bool>,

    /// The obligation we're currently in the process of executing.
    current_obligation: Option<ObligationIdx>,

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

struct ObligationState<K> {
    /// The obligation responsible for spawning this new obligation.
    parent: Option<ObligationIdx>,

    /// The number of parent obligations leading to the creation of this obligation.
    depth: u32,

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
            root: Rc::default(),
            local_obligation_queue: Rc::new(Vec::new()),
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
        Rc::make_mut(&mut self.local_obligation_queue).push(QueuedObligation {
            parent: self.root.current_obligation,
            kind,
        });
    }

    pub fn obligation_eval_suppressed(&self) -> bool {
        self.root.eval_suppressed.get()
    }

    pub fn set_obligation_eval_suppressed(&mut self, is_suppressed: bool) {
        self.root.eval_suppressed.set(is_suppressed);
    }

    pub fn poll_obligations<T>(
        target: &mut T,
        getter: impl Fn(&mut T) -> &mut Self,
        forker: impl Fn(&T) -> T,
        mut run: impl FnMut(&mut T, K) -> ObligationResult,
    ) {
        let this = getter(target);

        if this.root.current_obligation.is_some() || this.root.eval_suppressed.get() {
            return;
        }

        loop {
            let this = getter(target);

            let root = Rc::get_mut(&mut this.root)
                .expect("`ObligationCx` cannot be forked while polling obligations");

            debug_assert!(root.current_obligation.is_none());

            // Import queued obligations.
            for obligation in mem::take(Rc::make_mut(&mut this.local_obligation_queue)) {
                let QueuedObligation { parent, kind } = obligation;

                let depth = parent.map_or(0, |v| root.all_obligations[v].depth + 1);

                let obligation = root.all_obligations.push(ObligationState {
                    parent,
                    depth,
                    kind,
                    can_wake_by: FxHashSet::default(),
                });

                root.run_queue.push_back(obligation);
            }

            // See whether any new obligations can be added to the queue yet.
            for &var in &this.ucx.observed_infer_reveal_order()[root.rerun_var_read_len..] {
                let Some(awoken) = root.var_wake_ups.remove(&var) else {
                    continue;
                };

                for awoken_idx in awoken {
                    let awoken = &mut root.all_obligations[awoken_idx];

                    if !awoken.can_wake_by.contains(&var) {
                        continue;
                    }

                    awoken.can_wake_by.clear();

                    root.run_queue.push_back(awoken_idx);
                }
            }

            root.rerun_var_read_len = this.ucx.observed_infer_reveal_order().len();

            // Mark the next obligation as active.
            let Some(curr_idx) = root.run_queue.pop_front() else {
                break;
            };

            root.current_obligation = Some(curr_idx);

            let kind = root.all_obligations[curr_idx].kind.clone();

            // The `root` is set up so exclusive access to it is no longer needed; fork the
            // `target`.
            let mut fork = forker(target);

            // We must trace on the `fork` since stopping the tracing process requires exactly one
            // `UnifyCx` to remain.
            getter(&mut fork).ucx.start_tracing();

            // Process the obligation.
            let res = run(&mut fork, kind);

            // Interpret the result.
            let traced_vars = getter(&mut fork).ucx.finish_tracing();

            match res {
                ObligationResult::Success | ObligationResult::Failure(_) => {
                    // Merge the `fork` and the `target` and obtain the root.
                    *target = fork;
                    let this = getter(target);
                    let root = Rc::get_mut(&mut this.root).expect(
                        "All other `ObligationCx` forks must be dropped after obligation returns",
                    );

                    // Stop the obligation.
                    root.current_obligation = None;
                }
                ObligationResult::NotReady => {
                    // Drop the fork to regain access to the `root`.
                    drop(fork);
                    let this = getter(target);
                    let root = Rc::get_mut(&mut this.root).expect(
                        "All other `ObligationCx` forks must be dropped after obligation returns",
                    );

                    // Register wake-ups.
                    root.current_obligation = None;

                    let curr = &mut root.all_obligations[curr_idx];

                    for var in traced_vars {
                        if this.ucx.lookup_ty_infer_var(var).is_ok() {
                            continue;
                        }

                        let var = this.ucx.observe_ty_infer_var(var);

                        if !curr.can_wake_by.insert(var) {
                            continue;
                        }

                        root.var_wake_ups.entry(var).or_default().push(curr_idx);
                    }
                }
            }
        }
    }
}

// === Selection Helpers === //

pub type SelectionResult<T> = Result<ConfirmationResult<T>, SelectionRejected>;

#[derive(Debug, Clone)]
pub struct SelectionRejected;

#[derive(Clone)]
#[must_use]
pub enum ConfirmationResult<T> {
    Success(T),
    Error(ErrorGuaranteed),
}

impl<T> ConfirmationResult<T> {
    pub fn into_obligation_res(self, apply_target: &mut T) -> ObligationResult {
        match self {
            ConfirmationResult::Success(fork) => {
                *apply_target = fork;

                ObligationResult::Success
            }
            ConfirmationResult::Error(err) => ObligationResult::Failure(err),
        }
    }
}
