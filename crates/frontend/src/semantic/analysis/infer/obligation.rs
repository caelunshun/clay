use crate::{
    base::{Diag, HardDiag, Session, syntax::Span},
    semantic::{
        analysis::{ObservedTyVar, TyCtxt, UnifyCx, UnifyCxMode},
        syntax::{Re, TraitSpec, Ty},
    },
    utils::hash::{FxHashMap, FxHashSet},
};
use derive_where::derive_where;
use index_vec::{IndexVec, define_index_type};
use polonius_the_crab::{polonius, polonius_return};
use std::{
    cell::{Ref, RefCell},
    collections::VecDeque,
    fmt, mem,
    rc::Rc,
};

// === Definitions === //

pub const MAX_OBLIGATION_DEPTH: u32 = 256;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
#[must_use]
pub enum ShouldApplyFork {
    Yes,
    No,
}

impl ShouldApplyFork {
    #[must_use]
    pub fn should_apply(self) -> bool {
        matches!(self, Self::Yes)
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum ObligationKind {
    TyAndTrait(Ty, TraitSpec),
    TyAndRe(Ty, Re),
}

impl ObligationKind {
    // TODO
    pub fn proves_what(self, s: &Session) -> String {
        _ = s;
        format!("{self:?}")
    }
}

#[derive(Debug, Copy, Clone)]
pub enum ObligationReason {
    FunctionBody(Span),
    WfForTraitParam(Span),
    Structural,
}

#[derive(Debug, Clone)]
pub enum ObligationResult {
    /// The obligation was successfully satisfied.
    Success,

    /// The obligation is guaranteed to fail.
    Failure(HardDiag),

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
/// You can then poll these obligations for progress by following the following steps:
///
/// - Ensure that obligations are not being polled reentrantly using [`is_running_obligation`]. If
///   they are, early return and let the root-most call to your obligation polling function handle
///   them.
/// - While runnable obligations are still being returned by [`start_running_obligation`]...
///   - Fork the `ObligationCx` (and any other relevant contextual state) by `Clone`'ing it.
///   - Process the returned [`ObligationKind`] to obtain an [`ObligationResult`].
///   - Pass the result back to the `ObligationCx` using [`finish_running_obligation`].
///   - Use the returned [`ShouldApplyFork`] result to determine whether to apply the forked
///     state to `self` before solving another obligation.
///
/// This context can be forked while processing an obligation but, for efficiency purposes, does not
/// allow forking while not processing obligations.
///
/// [`push_obligation_no_poll`]: ObligationCx::push_obligation_no_poll
/// [`is_running_obligation`]: ObligationCx::is_running_obligation
/// [`start_running_obligation`]: ObligationCx::start_running_obligation
/// [`finish_running_obligation`]: ObligationCx::finish_running_obligation
#[derive(Clone)]
pub struct ObligationCx<'tcx> {
    ucx: UnifyCx<'tcx>,
    root: StealableRc<ObligationCxRoot>,
    local_obligation_queue: Rc<Vec<QueuedObligation>>,
}

#[derive(Clone)]
struct QueuedObligation {
    kind: ObligationKind,
    reason: ObligationReason,
}

#[derive(Default)]
struct ObligationCxRoot {
    /// The obligation we're currently in the process of executing.
    current_obligation: Option<ObligationIdx>,

    /// All obligations ever registered with us.
    all_obligations: IndexVec<ObligationIdx, ObligationState>,

    /// Every single obligation we've ever tried to prove. We only ever have to prove a given
    /// obligation and, if an obligation depends on itself, it is safe to assume it holds
    /// coinductively while proving itself.
    all_obligation_kinds: FxHashSet<ObligationKind>,

    /// The queue obligations to invoke. These are invoked in FIFO order to ensure that we properly
    /// explore all branches of the proof tree simultaneously.
    run_queue: VecDeque<ObligationIdx>,

    /// A map from inference variables to obligations they could re-run upon being inferred.
    var_wake_ups: FxHashMap<ObservedTyVar, Vec<ObligationIdx>>,

    /// The number of observed inference variables we have processed from `ucx`'s
    /// `observed_reveal_order` list.
    rerun_var_read_len: usize,
}

define_index_type! {
    struct ObligationIdx = u32;
}

struct ObligationState {
    /// The obligation responsible for spawning this new obligation.
    parent: Option<ObligationIdx>,

    /// The number of parent obligations leading to the creation of this obligation.
    depth: u32,

    /// The reason for which this obligation was spawned.
    reason: ObligationReason,

    /// The kind of obligation we're trying to prove.
    kind: ObligationKind,

    /// The set of variables whose inference could cause us to rerun. Cleared once the obligation is
    /// enqueued to re-run and re-populated if, after the re-run, the obligation is still ambiguous.
    can_wake_by: FxHashSet<ObservedTyVar>,
}

impl<'tcx> fmt::Debug for ObligationCx<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ObligationCx").finish_non_exhaustive()
    }
}

impl<'tcx> ObligationCx<'tcx> {
    pub fn new(tcx: &'tcx TyCtxt, mode: UnifyCxMode) -> Self {
        Self {
            ucx: UnifyCx::new(tcx, mode),
            root: StealableRc::default(),
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

    pub fn push_obligation_no_poll(&mut self, reason: ObligationReason, kind: ObligationKind) {
        if self.root.get_ref().current_obligation.is_none() {
            self.push_obligation_no_poll_immediately(None, reason, kind);
        } else {
            Rc::make_mut(&mut self.local_obligation_queue).push(QueuedObligation { kind, reason });
        }
    }

    fn push_obligation_no_poll_immediately(
        &mut self,
        parent: Option<ObligationIdx>,
        reason: ObligationReason,
        kind: ObligationKind,
    ) {
        let root = self.root.get_unique();

        if !root.all_obligation_kinds.insert(kind) {
            return;
        }

        let depth = parent.map_or(0, |v| root.all_obligations[v].depth + 1);

        if depth > MAX_OBLIGATION_DEPTH {
            // TODO: Improve diagnostic
            Diag::anon_err("maximum obligation depth reached").emit();
        }

        let obligation = root.all_obligations.push(ObligationState {
            parent,
            depth,
            reason,
            kind,
            can_wake_by: FxHashSet::default(),
        });

        root.run_queue.push_back(obligation);
    }

    #[must_use]
    pub fn is_running_obligation(&self) -> bool {
        self.root.get_ref().current_obligation.is_some()
    }

    #[must_use]
    pub fn start_running_obligation(&mut self) -> Option<ObligationKind> {
        let root = self.root.get_unique();

        debug_assert!(root.current_obligation.is_none());

        // See whether any new obligations can be added to the queue yet.
        for &var in &self.ucx.observed_reveal_order()[root.rerun_var_read_len..] {
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

        root.rerun_var_read_len = self.ucx.observed_reveal_order().len();

        // Start running the next obligation.
        let curr = root.run_queue.pop_front()?;
        root.current_obligation = Some(curr);

        self.ucx.start_tracing();

        Some(root.all_obligations[curr].kind)
    }

    pub fn finish_running_obligation(&mut self, result: ObligationResult) -> ShouldApplyFork {
        let root = self.root.get_unique();

        let curr_idx = root
            .current_obligation
            .take()
            .expect("not currently running an obligation");

        match result {
            ObligationResult::Success => {
                for obligation in mem::take(Rc::make_mut(&mut self.local_obligation_queue)) {
                    self.push_obligation_no_poll_immediately(
                        Some(curr_idx),
                        obligation.reason,
                        obligation.kind,
                    );
                }

                ShouldApplyFork::Yes
            }
            ObligationResult::Failure(diag) => {
                // TODO: Improve diagnostic
                diag.emit();

                ShouldApplyFork::No
            }
            ObligationResult::NotReady => {
                let curr = &mut root.all_obligations[curr_idx];

                for var in self.ucx.finish_tracing() {
                    if self.ucx.lookup_ty_var(var).is_ok() {
                        continue;
                    }

                    let var = self.ucx.observe_ty_var(var);

                    if !curr.can_wake_by.insert(var) {
                        continue;
                    }

                    root.var_wake_ups.entry(var).or_default().push(curr_idx);
                }

                ShouldApplyFork::No
            }
        }
    }
}

// === Selection Helpers === //

pub type SelectionResult<T> = Result<ConfirmationResult<T>, SelectionRejected>;

#[derive(Debug, Clone)]
pub struct SelectionRejected;

#[derive(Debug, Clone)]
#[must_use]
pub enum ConfirmationResult<T> {
    Success(T),
    Error(HardDiag),
}

impl<T> ConfirmationResult<T> {
    pub fn into_obligation_res(self, apply_target: &mut T) -> ObligationResult {
        match self {
            ConfirmationResult::Success(fork) => {
                *apply_target = fork;

                ObligationResult::Success
            }
            ConfirmationResult::Error(diag) => ObligationResult::Failure(diag),
        }
    }
}

// === Helpers === //

#[derive_where(Clone)]
struct StealableRc<T>(Rc<RefCell<Option<T>>>);

impl<T: Default> Default for StealableRc<T> {
    fn default() -> Self {
        Self::new(T::default())
    }
}

impl<T> StealableRc<T> {
    fn new(value: T) -> Self {
        Self(Rc::new(RefCell::new(Some(value))))
    }

    pub fn get_ref(&self) -> Ref<'_, T> {
        Ref::map(self.0.borrow(), |v| v.as_ref().expect("already stolen"))
    }

    pub fn get_unique(&mut self) -> &mut T {
        let mut this = &mut *self;

        polonius!(|this| -> &'polonius mut T {
            if let Some(unique) = Rc::get_mut(&mut this.0) {
                polonius_return!(unique.get_mut().as_mut().expect("already stolen"));
            }
        });

        let stolen = this.0.borrow_mut().take().expect("already stolen");

        this.0 = Rc::new(RefCell::new(Some(stolen)));

        Rc::get_mut(&mut this.0)
            .unwrap()
            .get_mut()
            .as_mut()
            .unwrap()
    }
}
