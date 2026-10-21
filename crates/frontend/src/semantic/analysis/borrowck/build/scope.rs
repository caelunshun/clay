use crate::semantic::{
    analysis::borrowck::build::traits::TraitCache,
    syntax::{
        MirBlockIdx, MirBody, MirLocal, MirLocalIdx, MirOperand, MirPlace, MirRvalue, MirScopeIdx,
        MirSourceInfo, MirStmt, MirStmtKind, MirTerminator, MirTerminatorKind, MirUnwindBehavior,
        TyCtxt,
    },
};
use slotmap::Key as _;

// === Aliases === //

#[derive(Debug, Copy, Clone)]
pub enum IfKind {
    IfTrue,
    IfFalse,
}

impl IfKind {
    pub fn trigger_on(cond: bool) -> Self {
        match cond {
            true => Self::IfTrue,
            false => Self::IfFalse,
        }
    }

    pub fn to_taken_not_taken<T>(self, blocks: [T; 2]) -> [T; 2] {
        let [taken, not_taken] = blocks;

        match self {
            IfKind::IfTrue => [taken, not_taken],
            IfKind::IfFalse => [not_taken, taken],
        }
    }
}

pub trait MirScopedBuilder<'tcx> {
    fn raw_builder(&mut self) -> &mut RawMirScopedBuilder<'tcx>;

    fn trait_cache(&mut self) -> &mut TraitCache<'tcx>;

    fn push_local(&mut self, expected_top: MirScopeIdx, local: MirLocal) -> MirLocalIdx {
        let can_omit_drop = self.trait_cache().can_omit_drop(local.ty);

        self.raw_builder()
            .push_local(expected_top, local, can_omit_drop)
    }

    fn push_assign(
        &mut self,
        expected_top: MirScopeIdx,
        source_info: MirSourceInfo,
        lhs: MirPlace,
        rhs: MirRvalue,
    ) {
        self.raw_builder().push_stmt(expected_top, || MirStmt {
            source_info,
            kind: MirStmtKind::Assign(Box::new((lhs, rhs))),
        });
    }

    fn push_call(
        &mut self,
        expected_top: MirScopeIdx,
        source_info: MirSourceInfo,
        destination: MirPlace,
        callee: MirOperand,
        args: impl IntoIterator<Item = MirOperand>,
    ) {
        self.raw_builder()
            .push_unwind_terminator(expected_top, |target, unwind| MirTerminator {
                debug_scope: expected_top,
                source_info,
                kind: MirTerminatorKind::Call {
                    callee,
                    args: args.into_iter().collect(),
                    destination,
                    target,
                    unwind,
                },
            });
    }

    fn push_unreachable(&mut self, expected_top: MirScopeIdx, source_info: MirSourceInfo) {
        self.raw_builder()
            .push_unreachable(expected_top, source_info);
    }

    fn push_break(
        &mut self,
        expected_top: MirScopeIdx,
        source_info: MirSourceInfo,
        target: MirScopeIdx,
    ) {
        self.raw_builder()
            .push_break(expected_top, source_info, target);
    }

    fn push_fallthrough(&mut self, expected_top: MirScopeIdx, source_info: MirSourceInfo) {
        self.raw_builder()
            .push_break(expected_top, source_info, expected_top);
    }

    fn push_continue(
        &mut self,
        expected_top: MirScopeIdx,
        source_info: MirSourceInfo,
        target: MirScopeIdx,
    ) {
        self.raw_builder()
            .push_continue(expected_top, source_info, target);
    }

    fn push_return(&mut self, expected_top: MirScopeIdx, source_info: MirSourceInfo) {
        self.raw_builder()
            .push_break(expected_top, source_info, MirScopeIdx::ENTRY);
    }

    fn push_scope(
        &mut self,
        expected_top: MirScopeIdx,
        source_info: MirSourceInfo,
        f: impl FnOnce(&mut Self, MirScopeIdx),
    ) {
        self.raw_builder().begin_branch(expected_top);

        let MirScopedBranch {
            scope: sub_scope,
            entry: sub_entry,
        } = self.raw_builder().add_branch_scope(expected_top);

        f(self, sub_scope);

        self.push_fallthrough(sub_scope, MirSourceInfo::BlockFallthrough);
        self.raw_builder().end_scope(sub_scope);

        self.raw_builder()
            .end_branch(expected_top, || MirTerminator {
                debug_scope: expected_top,
                source_info,
                kind: MirTerminatorKind::Goto(sub_entry),
            });
    }

    fn push_loop(
        &mut self,
        expected_top: MirScopeIdx,
        source_info: MirSourceInfo,
        f: impl FnOnce(&mut Self, MirScopeIdx),
    ) {
        self.push_scope(expected_top, source_info, |this, scope| {
            f(this, scope);
            this.push_continue(scope, source_info, scope);
        });
    }

    fn push_if(
        &mut self,
        expected_top: MirScopeIdx,
        source_info: MirSourceInfo,
        discr: MirOperand,
        kind: IfKind,
        if_taken: impl FnOnce(&mut Self, MirScopeIdx),
    ) {
        self.raw_builder().begin_branch(expected_top);
        let fallthrough = self.raw_builder().add_fallthrough_branch(expected_top);

        let MirScopedBranch {
            scope: sub_scope,
            entry: branch_entry,
        } = self.raw_builder().add_branch_scope(expected_top);

        if_taken(self, sub_scope);

        self.push_fallthrough(sub_scope, MirSourceInfo::BlockFallthrough);

        self.raw_builder().end_scope(sub_scope);

        self.raw_builder()
            .end_branch(expected_top, || MirTerminator {
                debug_scope: expected_top,
                source_info,
                kind: MirTerminatorKind::SwitchInt {
                    discr,
                    constants: [1, 0].into(),
                    targets: kind.to_taken_not_taken([branch_entry, fallthrough]).into(),
                },
            });
    }

    fn push_if_else(
        &mut self,
        expected_top: MirScopeIdx,
        source_info: MirSourceInfo,
        discr: MirOperand,
        kind: IfKind,
        if_taken: impl FnOnce(&mut Self, MirScopeIdx),
        if_not_taken: impl FnOnce(&mut Self, MirScopeIdx),
    ) {
        self.raw_builder().begin_branch(expected_top);

        let MirScopedBranch {
            scope: taken_scope,
            entry: taken_entry,
        } = self.raw_builder().add_branch_scope(expected_top);

        if_taken(self, taken_scope);

        self.push_fallthrough(taken_scope, MirSourceInfo::BlockFallthrough);

        self.raw_builder().end_scope(taken_scope);

        let MirScopedBranch {
            scope: not_taken_scope,
            entry: not_taken_entry,
        } = self.raw_builder().add_branch_scope(expected_top);

        if_not_taken(self, not_taken_scope);

        self.push_fallthrough(not_taken_scope, MirSourceInfo::BlockFallthrough);

        self.raw_builder().end_scope(not_taken_scope);

        self.raw_builder()
            .end_branch(expected_top, || MirTerminator {
                debug_scope: expected_top,
                source_info,
                kind: MirTerminatorKind::SwitchInt {
                    discr,
                    constants: [1, 0].into(),
                    targets: kind
                        .to_taken_not_taken([taken_entry, not_taken_entry])
                        .into(),
                },
            });
    }
}

pub struct MirScopedBuilderRef<'a, 'tcx> {
    pub raw_builder: &'a mut RawMirScopedBuilder<'tcx>,
    pub trait_cache: &'a mut TraitCache<'tcx>,
}

impl<'tcx> MirScopedBuilder<'tcx> for MirScopedBuilderRef<'_, 'tcx> {
    fn raw_builder(&mut self) -> &mut RawMirScopedBuilder<'tcx> {
        self.raw_builder
    }

    fn trait_cache(&mut self) -> &mut TraitCache<'tcx> {
        self.trait_cache
    }
}

// === RawMirScopedBuilder === //

pub struct RawMirScopedBuilder<'tcx> {
    tcx: &'tcx TyCtxt,
    body: MirBody,
    scope_id_gen: MirScopeIdx,
    scope_stack: Vec<BuilderScope>,
    live_locals: Vec<BuilderLocal>,
}

#[derive(Debug, Copy, Clone)]
pub struct MirScopedBranch {
    pub scope: MirScopeIdx,
    pub entry: MirBlockIdx,
}

struct BuilderScope {
    id: MirScopeIdx,
    live_state: Option<LiveBuilderScope>,
}

struct LiveBuilderScope {
    /// The index of the first local owned by this scope.
    first_live_local: u32,

    /// The latest unwind target we'll be chaining against when creating additional local drop
    /// targets.
    unwind_bb: MirBlockIdx,

    /// The entrypoint basic-block for this scope. Used for performing `continue` jumps.
    entry_bb: MirBlockIdx,

    /// The current-most basic block of logic for this scope. May be `None` if branching and we
    /// haven't yet proven that this scope is non-divergent.
    curr_bb: Option<MirBlockIdx>,

    /// The basic block to be initialized with our branching terminator or `None` if we're not
    /// actively creating branch sub-scopes.
    branch_bb: Option<MirBlockIdx>,
}

struct BuilderLocal {
    drop_unwind_target: Option<MirBlockIdx>,
    idx: MirLocalIdx,
}

impl<'tcx> RawMirScopedBuilder<'tcx> {
    pub fn new(
        tcx: &'tcx TyCtxt,
        return_local: MirLocal,
        can_omit_return_drop: bool,
        arg_count: u32,
    ) -> Self {
        let mut this = Self {
            tcx,
            body: MirBody::default(),
            scope_id_gen: MirScopeIdx::ENTRY + 1,
            scope_stack: Vec::new(),
            live_locals: Vec::new(),
        };

        this.body.arg_count = arg_count;

        let entry_bb = this.body.cfg.create_block();
        let return_local = this.body.locals.push(return_local);
        assert_eq!(return_local, MirLocalIdx::RETURN);

        let root_unwind_bb = this.body.cfg.create_block_with_terminator(MirTerminator {
            debug_scope: MirScopeIdx::UNCATEGORIZED,
            source_info: MirSourceInfo::Local(return_local),
            kind: MirTerminatorKind::UnwindResume,
        });

        let first_unwind_bb = if !can_omit_return_drop {
            // N.B. we do not register the return value as a local like all function arguments because
            // we don't want to drop it before a `return`. The only time we want to drop that place is
            // when we panic out of the function.
            this.body.cfg.create_block_with_terminator(MirTerminator {
                debug_scope: MirScopeIdx::UNCATEGORIZED,
                source_info: MirSourceInfo::Local(return_local),
                kind: MirTerminatorKind::EnsureDropped {
                    place: MirPlace::new(tcx, return_local, []),
                    target: root_unwind_bb,
                    unwind: MirUnwindBehavior::DoublePanic,
                },
            })
        } else {
            root_unwind_bb
        };

        this.body.entry = entry_bb;
        this.scope_stack.push(BuilderScope {
            id: MirScopeIdx::ENTRY,
            live_state: Some(LiveBuilderScope {
                first_live_local: 0,
                unwind_bb: first_unwind_bb,
                entry_bb,
                curr_bb: Some(entry_bb),
                branch_bb: None,
            }),
        });

        this
    }

    pub fn finish(self) -> MirBody {
        assert!(self.scope_stack.is_empty());
        self.body
    }
}

// Branch management
impl RawMirScopedBuilder<'_> {
    fn expect_top_ref(
        scope_stack: &[BuilderScope],
        expected_top: MirScopeIdx,
    ) -> Option<&LiveBuilderScope> {
        let top = scope_stack.last().expect("no active scope");
        assert_eq!(top.id, expected_top);

        top.live_state.as_ref()
    }

    fn expect_top_mut(
        scope_stack: &mut [BuilderScope],
        expected_top: MirScopeIdx,
    ) -> &mut Option<LiveBuilderScope> {
        let top = scope_stack.last_mut().expect("no active scope");
        assert_eq!(top.id, expected_top);

        &mut top.live_state
    }

    fn expect_live_pushing(top: &LiveBuilderScope) -> MirBlockIdx {
        assert!(
            top.branch_bb.is_none(),
            "cannot write code to a scope onto which branches are actively being pushed"
        );

        // Unwrap OK: only branching scopes may lack a successor
        top.curr_bb.unwrap()
    }

    fn kill_top(&mut self, expected_top: MirScopeIdx) {
        let top = Self::expect_top_mut(&mut self.scope_stack, expected_top)
            .take()
            .expect("top not live");

        self.live_locals.truncate(top.first_live_local as usize);
    }

    pub fn begin_branch(&mut self, expected_top: MirScopeIdx) {
        let Some(top) = Self::expect_top_mut(&mut self.scope_stack, expected_top) else {
            return;
        };

        let curr_bb = Self::expect_live_pushing(top);

        // Unwrap OK: only branching scopes may lack a successor
        top.curr_bb = None;
        top.branch_bb = Some(curr_bb);
    }

    pub fn add_fallthrough_branch(&mut self, expected_top: MirScopeIdx) -> MirBlockIdx {
        let Some(top) = Self::expect_top_mut(&mut self.scope_stack, expected_top) else {
            return MirBlockIdx::null();
        };

        assert!(
            top.branch_bb.is_some(),
            "must call `begin_branch` before `add_fallthrough_branch`"
        );

        *top.curr_bb
            .get_or_insert_with(|| self.body.cfg.create_block())
    }

    #[must_use]
    pub fn add_branch_scope(&mut self, expected_top: MirScopeIdx) -> MirScopedBranch {
        let Some(top) = Self::expect_top_ref(&self.scope_stack, expected_top) else {
            let sub_id = self.scope_id_gen;
            self.scope_id_gen += 1;

            self.scope_stack.push(BuilderScope {
                id: sub_id,
                live_state: None,
            });

            return MirScopedBranch {
                scope: sub_id,
                entry: MirBlockIdx::null(),
            };
        };

        assert!(
            top.branch_bb.is_some(),
            "must call `begin_branch` before `add_branch_scope`"
        );

        let sub_entry = self.body.cfg.create_block();
        let sub_id = self.scope_id_gen;
        self.scope_id_gen += 1;

        self.scope_stack.push(BuilderScope {
            id: sub_id,
            live_state: Some(LiveBuilderScope {
                first_live_local: self.live_locals.len() as u32,
                unwind_bb: top.unwind_bb,
                entry_bb: sub_entry,
                curr_bb: Some(sub_entry),
                branch_bb: None,
            }),
        });

        MirScopedBranch {
            scope: sub_id,
            entry: sub_entry,
        }
    }

    pub fn end_branch(
        &mut self,
        expected_top: MirScopeIdx,
        terminator: impl FnOnce() -> MirTerminator,
    ) {
        let Some(top) = Self::expect_top_mut(&mut self.scope_stack, expected_top) else {
            return;
        };

        let branch_bb = top
            .branch_bb
            .take()
            .expect("must call `begin_branch` before `end_branch`");

        let terminator = terminator();
        self.body.cfg.init_terminator(branch_bb, terminator);

        if top.curr_bb.is_none() {
            self.kill_top(expected_top);
        }
    }

    #[must_use]
    pub fn is_top_live(&self, expected_top: MirScopeIdx) -> bool {
        let top = Self::expect_top_ref(&self.scope_stack, expected_top);
        top.is_some()
    }

    #[must_use]
    pub fn is_top_dead(&self, expected_top: MirScopeIdx) -> bool {
        !self.is_top_live(expected_top)
    }

    pub fn end_scope(&mut self, expected_top: MirScopeIdx) {
        let top = Self::expect_top_ref(&self.scope_stack, expected_top);
        assert!(top.is_none(), "scope {expected_top:?} is still alive!");
        self.scope_stack.pop().unwrap();
    }
}

// Code pushing
impl RawMirScopedBuilder<'_> {
    pub fn push_unreachable(&mut self, expected_top: MirScopeIdx, source_info: MirSourceInfo) {
        let Some(top) = Self::expect_top_ref(&mut self.scope_stack, expected_top) else {
            return;
        };

        let curr_bb = Self::expect_live_pushing(top);

        self.body.cfg.init_terminator(
            curr_bb,
            MirTerminator {
                debug_scope: expected_top,
                source_info,
                kind: MirTerminatorKind::Unreachable,
            },
        );

        self.kill_top(expected_top);
    }

    pub fn push_break(
        &mut self,
        expected_top: MirScopeIdx,
        source_info: MirSourceInfo,
        target: MirScopeIdx,
    ) {
        self.push_break_common(expected_top, source_info, target, false);
    }

    pub fn push_continue(
        &mut self,
        expected_top: MirScopeIdx,
        source_info: MirSourceInfo,
        target: MirScopeIdx,
    ) {
        self.push_break_common(expected_top, source_info, target, true);
    }

    fn push_break_common(
        &mut self,
        expected_top: MirScopeIdx,
        source_info: MirSourceInfo,
        target: MirScopeIdx,
        is_continue: bool,
    ) {
        let Some(top) = Self::expect_top_ref(&mut self.scope_stack, expected_top) else {
            return;
        };

        let mut curr_bb = Self::expect_live_pushing(top);

        let mut scope_iter = self.scope_stack.iter_mut().rev();
        let mut local_iter = self.live_locals.iter().enumerate().rev().peekable();

        while let Some(top) = scope_iter.next() {
            let &BuilderScope {
                id: top_id,
                live_state: Some(ref top),
            } = &*top
            else {
                // If the top is live, so are all of its predecessors.
                unreachable!();
            };

            // Push drops.
            while let Some(&(live_local_idx, _)) = local_iter.peek()
                && live_local_idx as u32 >= top.first_live_local
            {
                let (_, local) = local_iter.next().unwrap();

                if let Some(unwind_if_drop_fails) = local.drop_unwind_target {
                    let successor = self.body.cfg.create_block();

                    self.body.cfg.init_terminator(
                        curr_bb,
                        MirTerminator {
                            debug_scope: expected_top,
                            source_info,
                            kind: MirTerminatorKind::EnsureDropped {
                                place: MirPlace::new(self.tcx, local.idx, []),
                                target: successor,
                                unwind: MirUnwindBehavior::Continue(unwind_if_drop_fails),
                            },
                        },
                    );

                    curr_bb = successor;
                }

                self.body.cfg.push_stmt(
                    curr_bb,
                    MirStmt {
                        source_info,
                        kind: MirStmtKind::StorageDead(local.idx),
                    },
                );
            }

            // If we've reached our target block, initialize the terminator.
            if top_id != target {
                continue;
            }

            match is_continue {
                true => {
                    // This is a `continue`. Jump back to the target's entrypoint.
                    let next_bb = top.entry_bb;

                    if curr_bb == next_bb {
                        // Terminators can never branch directly to themselves. To handle this special case—
                        // which should only happen for truly infinite loops (e.g. `loop {}`)!—we introduce a
                        // dummy block.
                        let spacer_block = self.body.cfg.create_block();

                        self.body.cfg.init_terminator(
                            curr_bb,
                            MirTerminator {
                                debug_scope: expected_top,
                                source_info,
                                kind: MirTerminatorKind::Goto(spacer_block),
                            },
                        );

                        curr_bb = spacer_block;
                    }

                    self.body.cfg.init_terminator(
                        curr_bb,
                        MirTerminator {
                            debug_scope: expected_top,
                            source_info,
                            kind: MirTerminatorKind::Goto(next_bb),
                        },
                    );
                }
                false => {
                    // This is a `break`. Jump to our parent's successor or return from the body.
                    match scope_iter.next() {
                        Some(successor) => {
                            // Unwrap OK: Same as above.
                            let successor = successor.live_state.as_mut().unwrap();

                            let next_bb = *successor
                                .curr_bb
                                .get_or_insert_with(|| self.body.cfg.create_block());

                            self.body.cfg.init_terminator(
                                curr_bb,
                                MirTerminator {
                                    debug_scope: expected_top,
                                    source_info,
                                    kind: MirTerminatorKind::Goto(next_bb),
                                },
                            );
                        }
                        None => {
                            self.body.cfg.init_terminator(
                                curr_bb,
                                MirTerminator {
                                    debug_scope: expected_top,
                                    source_info,
                                    kind: MirTerminatorKind::Return,
                                },
                            );
                        }
                    }
                }
            }

            self.kill_top(expected_top);
            return;
        }

        unreachable!("must break to ancestor");
    }

    #[must_use]
    pub fn push_local(
        &mut self,
        expected_top: MirScopeIdx,
        local: MirLocal,
        can_omit_drop: bool,
    ) -> MirLocalIdx {
        let Some(top) = Self::expect_top_mut(&mut self.scope_stack, expected_top) else {
            return MirLocalIdx::from_usize(MirLocalIdx::MAX_INDEX);
        };

        let curr = Self::expect_live_pushing(top);

        let local = self.body.locals.push(local);

        match can_omit_drop {
            true => {
                self.live_locals.push(BuilderLocal {
                    drop_unwind_target: None,
                    idx: local,
                });
            }
            false => {
                self.live_locals.push(BuilderLocal {
                    drop_unwind_target: Some(top.unwind_bb),
                    idx: local,
                });

                top.unwind_bb = self.body.cfg.create_block_with_terminator(MirTerminator {
                    debug_scope: MirScopeIdx::UNCATEGORIZED,
                    source_info: MirSourceInfo::Local(local),
                    kind: MirTerminatorKind::EnsureDropped {
                        place: MirPlace::new(self.tcx, local, []),
                        target: top.unwind_bb,
                        unwind: MirUnwindBehavior::DoublePanic,
                    },
                });
            }
        }

        self.body.cfg.push_stmt(
            curr,
            MirStmt {
                source_info: MirSourceInfo::Local(local),
                kind: MirStmtKind::StorageLive(local),
            },
        );

        local
    }

    pub fn push_stmt(&mut self, expected_top: MirScopeIdx, stmt: impl FnOnce() -> MirStmt) {
        let Some(top) = Self::expect_top_ref(&mut self.scope_stack, expected_top) else {
            return;
        };

        let curr = Self::expect_live_pushing(top);
        let stmt = stmt();

        self.body.cfg.push_stmt(curr, stmt);
    }

    pub fn push_unwind_terminator(
        &mut self,
        expected_top: MirScopeIdx,
        f: impl FnOnce(MirBlockIdx, MirUnwindBehavior) -> MirTerminator,
    ) {
        let Some(top) = Self::expect_top_mut(&mut self.scope_stack, expected_top) else {
            return;
        };

        let curr = Self::expect_live_pushing(top);

        let successor = self.body.cfg.create_block();
        let terminator = f(successor, MirUnwindBehavior::Continue(top.unwind_bb));
        self.body.cfg.init_terminator(curr, terminator);

        top.curr_bb = Some(successor);
    }
}
