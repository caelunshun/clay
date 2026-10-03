#![expect(dead_code)] // TODO

use crate::semantic::syntax::{
    MirBlock, MirBlockIdx, MirBody, MirLocal, MirLocalIdx, MirOperand, MirPlace, MirStmt,
    MirStmtKind, MirStmtSourceInfo, MirTerminator, MirUnwindBehavior, SigTy, TyCtxt,
};
use index_vec::{IndexVec, define_index_type};
use smallvec::SmallVec;

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
    scopes: IndexVec<MirBuilderScopeIdx, Scope>,
    body: MirBody,
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
    pub fn new(tcx: &'tcx TyCtxt) -> Self {
        let mut builder = Self {
            tcx,
            scopes: IndexVec::new(),
            body: MirBody::default(),
        };

        let entry_block = builder.body.blocks.push(MirBlock {
            stmts: Vec::new(),
            terminator: MirTerminator::Return,
            predecessors: SmallVec::new(),
            is_unwind: false,
        });
        let last_unwind_block = builder.body.blocks.push(MirBlock {
            stmts: Vec::new(),
            terminator: MirTerminator::UnwindResume,
            predecessors: SmallVec::new(),
            is_unwind: true,
        });

        assert_eq!(
            builder.scopes.push(Scope {
                parent: None,
                locals: Vec::new(),
                first_block: entry_block,
                curr_block: entry_block,
                curr_unwind_block: last_unwind_block,
            }),
            MirBuilderScopeIdx::BOOTSTRAP_ENTRY
        );

        assert_eq!(
            builder.push_scope(MirBuilderScopeIdx::BOOTSTRAP_ENTRY),
            MirBuilderScopeIdx::ENTRY
        );

        builder
    }

    /// Allocates a local in a scope, which is live for all descendant scopes.
    #[must_use]
    pub fn push_local(&mut self, scope: MirBuilderScopeIdx, ty: SigTy) -> MirLocalIdx {
        let mir_idx = self.body.locals.push(MirLocal { ty });

        let unwind_on_scope_drop_panic = self.requires_drop(ty).then(|| {
            let continue_unwind_bb = self.scopes[scope].curr_unwind_block;

            let drop_self_unwind_bb = self.body.blocks.push(MirBlock {
                stmts: Vec::new(),
                terminator: MirTerminator::EnsureDropped {
                    place: MirPlace::new(self.tcx, mir_idx, []),
                    target: continue_unwind_bb,
                    unwind: MirUnwindBehavior::DoublePanic,
                },
                predecessors: SmallVec::new(),
                is_unwind: true,
            });

            self.scopes[scope].curr_unwind_block = drop_self_unwind_bb;

            continue_unwind_bb
        });

        self.scopes[scope].locals.push(ScopeLocal {
            mir_idx,
            unwind_on_scope_drop_panic,
        });

        self.push_statement(
            scope,
            MirStmt {
                span: MirStmtSourceInfo::Local,
                kind: MirStmtKind::StorageLive(mir_idx),
            },
        );

        mir_idx
    }

    /// Pushes a regular statement to a scope.
    pub fn push_statement(&mut self, scope: MirBuilderScopeIdx, stmt: MirStmt) {
        self.body.blocks[self.scopes[scope].curr_block]
            .stmts
            .push(stmt);
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
        let returns_to = self.body.blocks.push(MirBlock {
            stmts: Vec::new(),
            terminator: MirTerminator::Placeholder,
            predecessors: SmallVec::new(),
            is_unwind: false,
        });
        self.scopes[scope].curr_block = returns_to;

        let successors = (0..succ_count)
            .map(|_| {
                let first_block = self.body.blocks.push(MirBlock {
                    stmts: Vec::new(),
                    terminator: MirTerminator::Placeholder,
                    predecessors: SmallVec::new(),
                    is_unwind: false,
                });

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

        self.body.blocks[branching_block].terminator = f(&successors
            .iter()
            .map(|&scope| self.scopes[scope].first_block)
            .collect::<SmallVec<[MirBlockIdx; 2]>>());

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
                    let scope_continue = self.body.blocks.push(MirBlock {
                        stmts: Vec::new(),
                        terminator: MirTerminator::Placeholder,
                        predecessors: SmallVec::new(),
                        is_unwind: false,
                    });

                    self.scopes[scope].curr_block = scope_continue;

                    self.body.blocks[scope_start].terminator = MirTerminator::EnsureDropped {
                        place: MirPlace::new(self.tcx, local.mir_idx, []),
                        target: scope_continue,
                        unwind: MirUnwindBehavior::Continue(unwind_on_scope_drop_panic),
                    };
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
        let dead_block = self.body.blocks.push(MirBlock {
            stmts: Vec::new(),
            terminator: MirTerminator::Placeholder,
            predecessors: SmallVec::new(),
            is_unwind: false,
        });
        self.scopes[scope].curr_block = dead_block;

        self.body.blocks[branching_block].terminator = MirTerminator::Goto(next_bb);
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

        let continue_bb = self.body.blocks.push(MirBlock {
            stmts: Vec::new(),
            terminator: MirTerminator::Placeholder,
            predecessors: SmallVec::new(),
            is_unwind: false,
        });

        self.scopes[scope].curr_block = continue_bb;
        self.body.blocks[start_bb].terminator =
            f(continue_bb, MirUnwindBehavior::Continue(unwind_bb));
    }

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
        let dead_block = self.body.blocks.push(MirBlock {
            stmts: Vec::new(),
            terminator: MirTerminator::Placeholder,
            predecessors: SmallVec::new(),
            is_unwind: false,
        });
        self.scopes[scope].curr_block = dead_block;

        self.body.blocks[branching_block].terminator = MirTerminator::Unreachable;
    }

    pub fn finish(mut self) -> MirBody {
        // Patch up the bootstrap entry.
        assert!(
            self.scopes[MirBuilderScopeIdx::BOOTSTRAP_ENTRY]
                .locals
                .is_empty()
        );

        self.body.blocks[self.scopes[MirBuilderScopeIdx::BOOTSTRAP_ENTRY].curr_block].terminator =
            MirTerminator::Return;

        // Optimize the control-flow graph
        self.cleanup_graph();

        self.body
    }
}

/// Trait detection
impl<'tcx> MirScopedBuilder<'tcx> {
    pub fn copy_or_move_operand(&mut self, place: MirPlace) -> MirOperand {
        // TODO: detect
        MirOperand::Move(place)
    }

    pub fn requires_drop(&mut self, ty: SigTy) -> bool {
        // TODO: detect
        true
    }
}
