use crate::{
    base::{HardDiag, Session, syntax::Span},
    semantic::{
        analysis::{InferCx, InferCxMode, ObservedTyVar, TyCtxt},
        syntax::{Re, TraitSpec, Ty},
    },
    utils::hash::{FxHashMap, FxHashSet},
};
use index_vec::{IndexVec, define_index_type};
use std::{collections::VecDeque, fmt, mem, rc::Rc};

// === Definitions === //

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

#[derive(Clone)]
pub struct ObligationCx<'tcx> {
    icx: InferCx<'tcx>,
    root: Rc<ObligationCxRoot>,
    local_obligation_queue: Rc<Vec<QueuedObligation>>,
}

#[derive(Clone)]
struct QueuedObligation {
    kind: ObligationKind,
    reason: ObligationReason,
}

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

    /// The number of observed inference variables we have processed from `icx`'s
    /// `observed_reveal_order` list.
    rerun_var_read_len: usize,

    /// The maximum depth we're willing to expand for obligations
    max_obligation_depth: u32,
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
    pub fn new(tcx: &'tcx TyCtxt, mode: InferCxMode, max_obligation_depth: u32) -> Self {
        Self {
            icx: InferCx::new(tcx, mode),
            root: Rc::new(ObligationCxRoot {
                current_obligation: None,
                all_obligations: IndexVec::new(),
                all_obligation_kinds: FxHashSet::default(),
                run_queue: VecDeque::new(),
                var_wake_ups: FxHashMap::default(),
                rerun_var_read_len: 0,
                max_obligation_depth,
            }),
            local_obligation_queue: Rc::new(Vec::new()),
        }
    }

    pub fn tcx(&self) -> &'tcx TyCtxt {
        self.icx.tcx()
    }

    pub fn session(&self) -> &'tcx Session {
        self.icx.session()
    }

    pub fn icx(&self) -> &InferCx<'tcx> {
        &self.icx
    }

    pub fn icx_mut(&mut self) -> &mut InferCx<'tcx> {
        &mut self.icx
    }

    pub fn push_obligation(&mut self, reason: ObligationReason, kind: ObligationKind) {
        if self.root.current_obligation.is_none() {
            self.push_obligation_immediately(None, reason, kind);
        } else {
            Rc::make_mut(&mut self.local_obligation_queue).push(QueuedObligation { kind, reason });
        }
    }

    fn push_obligation_immediately(
        &mut self,
        parent: Option<ObligationIdx>,
        reason: ObligationReason,
        kind: ObligationKind,
    ) {
        let root = Rc::get_mut(&mut self.root).expect(
            "`ObligationCx` cannot be forked and pushed to while no obligation is being resolved",
        );

        if root.all_obligation_kinds.insert(kind) {
            return;
        }

        let depth = parent.map_or(0, |v| root.all_obligations[v].depth + 1);

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
        self.root.current_obligation.is_some()
    }

    #[must_use]
    pub fn start_running_obligation(&mut self) -> Option<ObligationKind> {
        let root = Rc::get_mut(&mut self.root)
            .expect("`ObligationCx` cannot be forked while attempting to start a new obligation");

        debug_assert!(root.current_obligation.is_none());

        // See whether any new obligations can be added to the queue yet.
        for &var in &self.icx.observed_reveal_order()[root.rerun_var_read_len..] {
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

        root.rerun_var_read_len = self.icx.observed_reveal_order().len();

        // Start running the next obligation.
        let curr = root.run_queue.pop_front()?;
        root.current_obligation = Some(curr);

        self.icx.start_tracing();

        Some(root.all_obligations[curr].kind)
    }

    pub fn finish_running_obligation(&mut self, result: ObligationResult) -> ShouldApplyFork {
        let root = Rc::get_mut(&mut self.root)
            .expect("`ObligationCx` cannot be forked while attempting to finish an old obligation");

        let curr_idx = root
            .current_obligation
            .take()
            .expect("not currently running an obligation");

        match result {
            ObligationResult::Success => {
                for obligation in mem::take(Rc::make_mut(&mut self.local_obligation_queue)) {
                    self.push_obligation_immediately(
                        Some(curr_idx),
                        obligation.reason,
                        obligation.kind,
                    );
                }

                ShouldApplyFork::Yes
            }
            ObligationResult::Failure(diag) => {
                // TODO: Diagnostic
                diag.emit();

                ShouldApplyFork::No
            }
            ObligationResult::NotReady => {
                let curr = &mut root.all_obligations[curr_idx];

                for var in self.icx.finish_tracing() {
                    if self.icx.lookup_ty_var(var).is_ok() {
                        continue;
                    }

                    let var = self.icx.observe_ty_var(var);

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

pub type SelectionResult = Result<ConfirmationResult, SelectionRejected>;

#[derive(Debug, Clone)]
pub struct SelectionRejected;

#[derive(Debug, Clone)]
#[must_use]
pub enum ConfirmationResult {
    Success,
    Error(HardDiag),
}

impl ConfirmationResult {
    pub fn into_obligation_res(self) -> ObligationResult {
        match self {
            ConfirmationResult::Success => ObligationResult::Success,
            ConfirmationResult::Error(diag) => ObligationResult::Failure(diag),
        }
    }
}
