use crate::{
    bool_enum,
    semantic::{
        analysis::borrowck::scopes::{
            CanOmitDrop,
            drops::{CanPreinsertLocals, DropNodeIdx, DropScheduler, JumpTarget},
        },
        syntax::{
            MirBlockIdx, MirBody, MirLocal, MirLocalIdx, MirPlace, MirScopeIdx, MirSourceInfo,
            MirStmt, MirStmtKind, MirTerminator, MirTerminatorKind, MirUnwindBehavior, TyCtxt,
        },
    },
};
use slotmap::Key as _;

bool_enum! {
    pub enum CanHoistLocals {
        true => Yes;
        false => No;
    }
}

pub struct RawMirScopedBuilder<'tcx> {
    tcx: &'tcx TyCtxt,
    body: MirBody,
    drop_scheduler: DropScheduler,
    scope_id_gen: MirScopeIdx,
    scope_stack: Vec<BuilderScope>,
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
    /// Whether `push_local` can hoist locals into this scope.
    can_hoist_locals: CanHoistLocals,

    /// If the scope is the top-most live scope, this points to the most recently added local (or
    /// the root scope if we haven't added any locals yet). If is a scope actively building a
    /// branched child, this points to a scope node for the child scope. This node is never
    /// root-most to allow us to insert new locals after it and to run `scope_successor`.
    head_local: DropNodeIdx,

    /// The entrypoint basic-block for this scope. Used for performing `continue` jumps.
    entry_bb: MirBlockIdx,

    /// The current-most basic block of logic for this scope. May be `None` if branching and we
    /// haven't yet proven that this scope is non-divergent.
    curr_bb: Option<MirBlockIdx>,

    /// The basic block to be initialized with our branching terminator or `None` if we're not
    /// actively creating branch sub-scopes.
    branch_bb: Option<MirBlockIdx>,
}

impl<'tcx> RawMirScopedBuilder<'tcx> {
    pub fn new(
        tcx: &'tcx TyCtxt,
        return_local: MirLocal,
        can_omit_return_drop: CanOmitDrop,
        arg_count: u32,
    ) -> Self {
        let mut this = Self {
            tcx,
            body: MirBody::default(),
            drop_scheduler: DropScheduler::default(),
            scope_id_gen: MirScopeIdx::ENTRY + 1,
            scope_stack: Vec::new(),
        };

        let entry_bb = this.body.cfg.create_block();
        this.body.entry = entry_bb;

        let return_local = this.body.locals.push(return_local);
        this.body.arg_count = arg_count;
        assert_eq!(return_local, MirLocalIdx::RETURN);

        let mut root_unwind_bb = this.body.cfg.create_block_with_terminator(MirTerminator {
            debug_scope: MirScopeIdx::UNCATEGORIZED,
            source_info: MirSourceInfo::Local(return_local),
            kind: MirTerminatorKind::UnwindResume,
        });

        if can_omit_return_drop.is_truthy() {
            // N.B. we do not register the return value as a local like all function arguments because
            // we don't want to drop it before a `return`. The only time we want to drop that place is
            // when we panic out of the function.
            root_unwind_bb = this.body.cfg.create_block_with_terminator(MirTerminator {
                debug_scope: MirScopeIdx::UNCATEGORIZED,
                source_info: MirSourceInfo::Local(return_local),
                kind: MirTerminatorKind::EnsureDropped {
                    place: MirPlace::new(tcx, return_local, []),
                    target: root_unwind_bb,
                    unwind: MirUnwindBehavior::DoublePanic,
                },
            })
        }

        this.drop_scheduler
            .init_unwind_fallthrough_bb(root_unwind_bb);

        this.scope_stack.push(BuilderScope {
            id: MirScopeIdx::ENTRY,
            live_state: Some(LiveBuilderScope {
                can_hoist_locals: CanHoistLocals::Yes,
                head_local: DropNodeIdx::ROOT,
                entry_bb,
                curr_bb: Some(entry_bb),
                branch_bb: None,
            }),
        });

        this
    }

    pub fn finish(mut self) -> MirBody {
        self.end_scope(MirScopeIdx::ENTRY);
        self.drop_scheduler.finish(self.tcx, &mut self.body);
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
        assert_eq!(top.id, expected_top, "mismatched top scope");

        top.live_state.as_ref()
    }

    fn expect_top_mut(
        scope_stack: &mut [BuilderScope],
        expected_top: MirScopeIdx,
    ) -> &mut Option<LiveBuilderScope> {
        let top = scope_stack.last_mut().expect("no active scope");
        assert_eq!(top.id, expected_top, "mismatched top scope");

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

    fn mark_top_as_dead(&mut self, expected_top: MirScopeIdx) {
        Self::expect_top_mut(&mut self.scope_stack, expected_top)
            .take()
            .expect("top not live");

        let Some(parent) = self.scope_stack.iter_mut().nth_back(1) else {
            return;
        };

        // Unwrap OK: all ancestor scopes must also be live.
        let parent = parent.live_state.as_mut().unwrap();

        parent.head_local = self.drop_scheduler.scope_successor(parent.head_local);
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

    pub fn add_branch_scope(
        &mut self,
        expected_top: MirScopeIdx,
        can_hoist_locals: CanHoistLocals,
    ) -> MirScopedBranch {
        let Some(top) = Self::expect_top_mut(&mut self.scope_stack, expected_top) else {
            // Create a dummy child scope.
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

        let sub_id = self.scope_id_gen;
        self.scope_id_gen += 1;

        // Create a drop node for the scope. This will be pushed once the child becomes dead.
        let extensible = match top.can_hoist_locals {
            CanHoistLocals::Yes => CanPreinsertLocals::Yes,
            CanHoistLocals::No => CanPreinsertLocals::No,
        };

        let new_head_local = self
            .drop_scheduler
            .push_scope(sub_id, extensible, top.head_local);

        top.head_local = new_head_local;

        // Create the child scope
        let sub_entry = self.body.cfg.create_block();

        self.scope_stack.push(BuilderScope {
            id: sub_id,
            live_state: Some(LiveBuilderScope {
                can_hoist_locals,
                head_local: new_head_local,
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
            self.mark_top_as_dead(expected_top);
        }
    }

    pub fn is_top_live(&self, expected_top: MirScopeIdx) -> bool {
        let top = Self::expect_top_ref(&self.scope_stack, expected_top);
        top.is_some()
    }

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

        self.mark_top_as_dead(expected_top);
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

        let curr_bb = Self::expect_live_pushing(top);
        let top_head_local = top.head_local;

        // Find the target basic block without the jump chain
        let jump_target = 'jump_target: {
            let mut iter = self.scope_stack.iter_mut().rev();

            while let Some(scope) = iter.next() {
                if scope.id != target {
                    continue;
                }

                break 'jump_target match is_continue {
                    true => {
                        // Unwrap OK: all ancestors of a live scope are live
                        let scope_live = scope.live_state.as_mut().unwrap();

                        JumpTarget::Goto(scope_live.entry_bb)
                    }
                    false => {
                        if let Some(scope) = iter.next() {
                            // Unwrap OK: all ancestors of a live scope are live
                            let scope_live = scope.live_state.as_mut().unwrap();

                            JumpTarget::Goto(
                                *scope_live
                                    .curr_bb
                                    .get_or_insert_with(|| self.body.cfg.create_block()),
                            )
                        } else {
                            JumpTarget::Return
                        }
                    }
                };
            }

            panic!("target scope is not an ancestor");
        };

        let jump_bb =
            self.drop_scheduler
                .request_jump(jump_target, top_head_local, target, &mut self.body);

        self.body.cfg.init_terminator(
            curr_bb,
            MirTerminator {
                debug_scope: expected_top,
                source_info,
                kind: MirTerminatorKind::Goto(jump_bb),
            },
        );

        self.mark_top_as_dead(expected_top);
    }

    pub fn push_local(
        &mut self,
        in_scope: MirScopeIdx,
        local: MirLocal,
        can_omit_drop: CanOmitDrop,
    ) -> MirLocalIdx {
        let (top, parents) = self.scope_stack.split_last_mut().unwrap();

        // Handle local creation on top scope
        if top.id == in_scope {
            let Some(top) = &mut top.live_state else {
                return MirLocalIdx::from_raw(u32::MAX);
            };

            let local = self.body.locals.push(local);

            top.head_local =
                self.drop_scheduler
                    .push_local_top(local, can_omit_drop, top.head_local);

            let insert_into = top.branch_bb.unwrap_or_else(|| {
                // Unwrap OK: `curr_bb` is present on live scopes so long as we're not branching.
                top.curr_bb.unwrap()
            });

            self.body.cfg.push_stmt(
                insert_into,
                MirStmt {
                    source_info: MirSourceInfo::Todo,
                    kind: MirStmtKind::StorageLive(local),
                },
            );

            return local;
        };

        // Handle local creation on ancestor scopes
        let parent = parents
            .iter()
            .rev()
            .find(|v| v.id == in_scope)
            .expect("in_scope is not an ancestor of the top scope");

        let Some(parent) = &parent.live_state else {
            return MirLocalIdx::from_raw(u32::MAX);
        };

        let local = self.body.locals.push(local);

        self.drop_scheduler
            .push_local_after(parent.head_local, local, can_omit_drop);

        self.body.cfg.push_stmt(
            // Unwrap OK: only branching scopes can have children.
            parent.branch_bb.unwrap(),
            MirStmt {
                source_info: MirSourceInfo::Todo,
                kind: MirStmtKind::StorageLive(local),
            },
        );

        local
    }

    pub fn can_hoist_local_into(&self, in_scope: MirScopeIdx) -> bool {
        self.scope_stack
            .iter()
            .rev()
            .find_map(|scope| {
                if scope.id != in_scope {
                    return None;
                }

                let Some(scope) = &scope.live_state else {
                    // We blanket-allow these operations.
                    return Some(true);
                };

                Some(scope.can_hoist_locals.is_truthy())
            })
            .expect("in_scope is not an ancestor of the top scope")
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
        let unwind_bb = self
            .drop_scheduler
            .request_unwind(top.head_local, &mut self.body);

        let terminator = f(successor, MirUnwindBehavior::Continue(unwind_bb));
        self.body.cfg.init_terminator(curr, terminator);

        top.curr_bb = Some(successor);
    }
}
