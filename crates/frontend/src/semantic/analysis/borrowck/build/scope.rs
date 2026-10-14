use crate::{
    base::{Session, arena::Obj},
    flags,
    semantic::syntax::{
        FnDef, MirBlockIdx, MirBody, MirLocal, MirLocalIdx, MirOperand, MirOperandMode, MirPlace,
        MirStmt, MirStmtKind, MirStmtSourceInfo, MirTerminator, MirUnwindBehavior, SigTy, TyCtxt,
    },
};
use index_vec::{IndexVec, define_index_type};
use smallvec::SmallVec;
use std::{
    fmt::{self, Write as _},
    panic::Location,
};

// === Building === //

define_index_type! {
    pub struct MirBuilderScopeIdx = u32;
}

impl MirBuilderScopeIdx {
    // The actual root scope. Does not have locals of its own and never exposed to the user to
    // ensure that returns can be represented as regular breaks.
    const BOOTSTRAP_ENTRY: MirBuilderScopeIdx = MirBuilderScopeIdx { _raw: 0 };

    pub const ENTRY: MirBuilderScopeIdx = MirBuilderScopeIdx { _raw: 1 };
}

define_index_type! {
    struct BranchIdx = u32;
}

pub struct MirScopedBuilder<'tcx> {
    tcx: &'tcx TyCtxt,
    def: Obj<FnDef>,
    body: MirBody,
    scopes: IndexVec<MirBuilderScopeIdx, Scope>,
    debug: Option<MirScopeBodyDebug>,
}

struct Scope {
    parent: Option<ScopeParent>,
    locals: Vec<ScopeLocal>,
    first_block: MirBlockIdx,
    curr_block: MirBlockIdx,
    curr_unwind_block: MirBlockIdx,
}

#[derive(Copy, Clone)]
struct ScopeLocal {
    mir_idx: MirLocalIdx,
    unwind_on_scope_drop_panic: Option<MirBlockIdx>,
}

#[derive(Copy, Clone)]
struct ScopeParent {
    target: MirBuilderScopeIdx,
    returns_to: MirBlockIdx,
    last_local: usize,
}

/// Machinery
impl<'tcx> MirScopedBuilder<'tcx> {
    pub fn new(tcx: &'tcx TyCtxt, def: Obj<FnDef>) -> Self {
        let s = &tcx.session;

        let body = {
            let mut body = MirBody::default();

            body.locals.push(MirLocal {
                ty: *def.r(s).ret_ty,
            });

            for arg in def.r(s).args.r(s) {
                body.locals.push(MirLocal { ty: arg.ty });
            }

            body
        };

        let mut this = Self {
            tcx,
            def,
            body,
            scopes: IndexVec::new(),
            debug: flags::should_print_mir_scopes().then(MirScopeBodyDebug::default),
        };

        let last_unwind_block = this
            .body
            .cfg
            .create_block_with_terminator(MirTerminator::UnwindResume);

        assert_eq!(
            this.scopes.push(Scope {
                parent: None,
                locals: Vec::new(),
                first_block: this.body.entry,
                curr_block: this.body.entry,
                curr_unwind_block: last_unwind_block,
            }),
            MirBuilderScopeIdx::BOOTSTRAP_ENTRY
        );

        assert_eq!(
            this.push_scope(MirBuilderScopeIdx::BOOTSTRAP_ENTRY),
            MirBuilderScopeIdx::ENTRY
        );

        if let Some(debug) = &mut this.debug {
            debug.push_prose(
                MirBuilderScopeIdx::ENTRY,
                format_args!(
                    "// BB {:?}",
                    this.scopes[MirBuilderScopeIdx::ENTRY].curr_block
                ),
            );
        }

        this
    }

    pub fn session(&self) -> &'tcx Session {
        &self.tcx.session
    }

    pub fn tcx(&self) -> &'tcx TyCtxt {
        self.tcx
    }

    pub fn def(&self) -> Obj<FnDef> {
        self.def
    }

    /// Allocates a local in a scope, which is live for all descendant scopes.
    #[track_caller]
    #[must_use]
    pub fn push_local(&mut self, scope: MirBuilderScopeIdx, info: MirLocal) -> MirLocalIdx {
        let mir_idx = self.body.locals.push(info);

        let unwind_on_scope_drop_panic = self.requires_drop(info.ty).then(|| {
            let continue_unwind_bb = self.scopes[scope].curr_unwind_block;

            let drop_self_unwind_bb =
                self.body
                    .cfg
                    .create_block_with_terminator(MirTerminator::EnsureDropped {
                        place: MirPlace::new(self.tcx, mir_idx, []),
                        target: continue_unwind_bb,
                        unwind: MirUnwindBehavior::DoublePanic,
                    });

            self.scopes[scope].curr_unwind_block = drop_self_unwind_bb;

            continue_unwind_bb
        });

        self.scopes[scope].locals.push(ScopeLocal {
            mir_idx,
            unwind_on_scope_drop_panic,
        });

        self.body.cfg.push_stmt(
            self.scopes[scope].curr_block,
            MirStmt {
                span: MirStmtSourceInfo::Local,
                kind: MirStmtKind::StorageLive(mir_idx),
            },
        );

        if let Some(debug) = &mut self.debug {
            debug.push_prose(
                scope,
                format_args!(
                    "let _{}: {:?};  // {}",
                    mir_idx.index(),
                    info.ty,
                    Location::caller()
                ),
            );
        }

        mir_idx
    }

    /// Pushes a regular statement to a scope.
    #[track_caller]
    pub fn push_statement(&mut self, scope: MirBuilderScopeIdx, stmt: MirStmt) {
        if let Some(debug) = &mut self.debug {
            match &stmt.kind {
                MirStmtKind::StorageLive(local) => {
                    debug.push_prose(
                        scope,
                        format_args!(
                            "StorageLive(_{});  // {}",
                            local.index(),
                            Location::caller()
                        ),
                    );
                }
                MirStmtKind::StorageDead(local) => {
                    debug.push_prose(
                        scope,
                        format_args!(
                            "StorageDead(_{});  // {}",
                            local.index(),
                            Location::caller()
                        ),
                    );
                }
                MirStmtKind::Assign(stmt) => todo!(),
                MirStmtKind::DiscardWithoutDrop(rvalue) => todo!(),
            }
        }

        self.body.cfg.push_stmt(self.scopes[scope].curr_block, stmt);
    }

    /// Pushes a terminator that branches into some number of child scopes. This can handle diverging
    /// terminators where the successor count is zero and unconditional scope entries where the
    /// successor count is one (e.g. `loop` entries) but cannot handle jumps out of the current
    /// scope, which must be done with [`Self::push_break`] and [`Self::push_continue`].
    #[must_use]
    fn push_branch_dyn(
        &mut self,
        scope: MirBuilderScopeIdx,
        succ_count: usize,
        f: impl FnOnce(&[MirBlockIdx]) -> MirTerminator,
    ) -> SmallVec<[MirBuilderScopeIdx; 2]> {
        let branching_block = self.scopes[scope].curr_block;
        let continue_parent_unwind = self.scopes[scope].curr_unwind_block;

        let returns_to = self.body.cfg.create_block();
        self.scopes[scope].curr_block = returns_to;

        let successors = (0..succ_count)
            .map(|_| {
                let first_block = self.body.cfg.create_block();

                self.scopes.push(Scope {
                    parent: Some(ScopeParent {
                        target: scope,
                        returns_to,
                        last_local: self.scopes[scope].locals.len(),
                    }),
                    locals: Vec::new(),
                    first_block,
                    curr_block: first_block,
                    curr_unwind_block: continue_parent_unwind,
                })
            })
            .collect::<SmallVec<[MirBuilderScopeIdx; 2]>>();

        self.body.cfg.init_terminator(
            branching_block,
            f(&successors
                .iter()
                .map(|&scope| self.scopes[scope].first_block)
                .collect::<SmallVec<[MirBlockIdx; 2]>>()),
        );

        successors
    }

    #[must_use]
    fn push_branch_fixed<const N: usize>(
        &mut self,
        scope: MirBuilderScopeIdx,
        f: impl FnOnce([MirBlockIdx; N]) -> MirTerminator,
    ) -> [MirBuilderScopeIdx; N] {
        *self
            .push_branch_dyn(scope, N, |indices| f(*indices.as_array().unwrap()))
            .as_array()
            .unwrap()
    }

    fn push_break_shared(
        &mut self,
        scope: MirBuilderScopeIdx,
        target: MirBuilderScopeIdx,
        next_bb: MirBlockIdx,
    ) {
        // Push `StorageDead` statements.
        #[derive(Copy, Clone)]
        struct IterState {
            scope: MirBuilderScopeIdx,
            last_local: usize,
        }

        let mut next = IterState {
            scope,
            last_local: self.scopes[scope].locals.len(),
        };

        loop {
            let curr = next;

            for idx in (0..curr.last_local).rev() {
                let local = self.scopes[curr.scope].locals[idx];

                if let Some(unwind_on_scope_drop_panic) = local.unwind_on_scope_drop_panic {
                    let scope_start = self.scopes[scope].curr_block;
                    let scope_continue = self.body.cfg.create_block();

                    self.scopes[scope].curr_block = scope_continue;

                    self.body.cfg.init_terminator(
                        scope_start,
                        MirTerminator::EnsureDropped {
                            place: MirPlace::new(self.tcx, local.mir_idx, []),
                            target: scope_continue,
                            unwind: MirUnwindBehavior::Continue(unwind_on_scope_drop_panic),
                        },
                    );
                }

                self.push_statement(
                    scope,
                    MirStmt {
                        span: MirStmtSourceInfo::Break,
                        kind: MirStmtKind::StorageDead(local.mir_idx),
                    },
                );
            }

            if curr.scope == target {
                break;
            }

            let parent = self.scopes[curr.scope].parent.expect("not an ancestor");

            next = IterState {
                scope: parent.target,
                last_local: parent.last_local,
            };
        }

        // Push terminator.
        let branching_block = self.scopes[scope].curr_block;
        let dead_block = self.body.cfg.create_block();
        self.scopes[scope].curr_block = dead_block;

        self.body
            .cfg
            .init_terminator(branching_block, MirTerminator::Goto(next_bb));
    }

    /// Finishes the current scope by breaking out to a target which must be an ancestor scope.
    pub fn push_break(&mut self, scope: MirBuilderScopeIdx, target: MirBuilderScopeIdx) {
        self.push_break_shared(scope, target, self.scopes[scope].parent.unwrap().returns_to);
    }

    /// Finishes the current scope by jumping back to the start of an ancestor scope.
    pub fn push_continue(&mut self, scope: MirBuilderScopeIdx, target: MirBuilderScopeIdx) {
        self.push_break_shared(scope, target, self.scopes[scope].first_block);
    }

    fn push_unwind_terminator(
        &mut self,
        scope: MirBuilderScopeIdx,
        f: impl FnOnce(MirBlockIdx, MirUnwindBehavior) -> MirTerminator,
    ) {
        let start_bb = self.scopes[scope].curr_block;
        let unwind_bb = self.scopes[scope].curr_unwind_block;

        let continue_bb = self.body.cfg.create_block();

        self.scopes[scope].curr_block = continue_bb;
        self.body.cfg.init_terminator(
            start_bb,
            f(continue_bb, MirUnwindBehavior::Continue(unwind_bb)),
        );
    }

    // TODO: use this, not the discard rvalue statement.
    pub fn push_drop(&mut self, scope: MirBuilderScopeIdx, place: MirPlace) {
        self.push_unwind_terminator(scope, |target, unwind| MirTerminator::EnsureDropped {
            place,
            target,
            unwind,
        });
    }

    pub fn push_call(
        &mut self,
        scope: MirBuilderScopeIdx,
        callee: MirOperand,
        args: Box<[MirOperand]>,
        destination: MirPlace,
    ) {
        self.push_unwind_terminator(scope, |target, unwind| MirTerminator::Call {
            callee,
            args,
            destination,
            target,
            unwind,
        });
    }

    #[must_use]
    pub fn push_scope(&mut self, scope: MirBuilderScopeIdx) -> MirBuilderScopeIdx {
        let [sub_scope] = self.push_branch_fixed(scope, |[target]| MirTerminator::Goto(target));
        sub_scope
    }

    #[must_use]
    pub fn push_switch_dyn<const N: usize>(
        &mut self,
        scope: MirBuilderScopeIdx,
        discr: MirOperand,
        constants: &[u64],
    ) -> SmallVec<[MirBuilderScopeIdx; 2]> {
        self.push_branch_dyn(scope, constants.len(), |matchers| {
            MirTerminator::SwitchInt {
                discr,
                constants: Box::from_iter(constants.iter().copied()),
                targets: Box::from_iter(matchers.iter().copied()),
            }
        })
    }

    #[must_use]
    pub fn push_switch_fixed<const N: usize>(
        &mut self,
        scope: MirBuilderScopeIdx,
        discr: MirOperand,
        constants: [u64; N],
    ) -> [MirBuilderScopeIdx; N] {
        self.push_branch_fixed::<N>(scope, |matchers| MirTerminator::SwitchInt {
            discr,
            constants: Box::from_iter(constants),
            targets: Box::from_iter(matchers.iter().copied()),
        })
    }

    pub fn push_return(&mut self, scope: MirBuilderScopeIdx) {
        self.push_break(scope, MirBuilderScopeIdx::ENTRY);
    }

    pub fn push_unreachable(&mut self, scope: MirBuilderScopeIdx) {
        let branching_block = self.scopes[scope].curr_block;
        let dead_block = self.body.cfg.create_block();
        self.scopes[scope].curr_block = dead_block;
        self.body
            .cfg
            .init_terminator(branching_block, MirTerminator::Unreachable);
    }

    pub fn finish(mut self) -> MirBody {
        assert!(
            self.scopes[MirBuilderScopeIdx::BOOTSTRAP_ENTRY]
                .locals
                .is_empty()
        );

        self.body.cfg.init_terminator(
            self.scopes[MirBuilderScopeIdx::BOOTSTRAP_ENTRY].curr_block,
            MirTerminator::Return,
        );

        self.body.cfg.prune_unreachable(self.body.entry);

        self.body
    }
}

/// Trait detection
impl<'tcx> MirScopedBuilder<'tcx> {
    pub fn operand_mode(&mut self, ty: SigTy) -> MirOperandMode {
        // TODO: detect
        MirOperandMode::Move
    }

    pub fn requires_drop(&mut self, ty: SigTy) -> bool {
        // TODO: detect
        true
    }
}

// === Debug Info === //

#[derive(Clone, Default)]
pub struct MirScopeBodyDebug {
    annotations: IndexVec<MirBuilderScopeIdx, Vec<MirScopeDebugEntry>>,
}

#[derive(Clone)]
pub enum MirScopeDebugEntry {
    Prose(String),
    Block(MirBuilderScopeIdx),
}

impl MirScopeBodyDebug {
    pub fn push_prose_inline(&mut self, scope: MirBuilderScopeIdx, text: impl fmt::Display) {
        if scope.index() >= self.annotations.len() {
            self.annotations.resize(scope.index() + 1, Vec::new());
        }

        if let Some(MirScopeDebugEntry::Prose(existing)) = self.annotations[scope].last_mut() {
            write!(existing, "{text}").unwrap();
        } else {
            self.annotations[scope].push(MirScopeDebugEntry::Prose(text.to_string()));
        }
    }

    pub fn push_prose(&mut self, scope: MirBuilderScopeIdx, text: impl fmt::Display) {
        self.push_prose_inline(scope, format_args!("{text}\n"));
    }

    pub fn push_child(&mut self, scope: MirBuilderScopeIdx, child: MirBuilderScopeIdx) {
        if scope.index() >= self.annotations.len() {
            self.annotations.resize(scope.index() + 1, Vec::new());
        }

        self.annotations[scope].push(MirScopeDebugEntry::Block(child));
    }
}
