use crate::semantic::syntax::{
    Divergence, MirBlockIdx, MirBody, MirLocalIdx, MirPlace, MirStmt, MirStmtKind,
    MirStmtSourceInfo, MirTerminator, MirUnwindBehavior, TyCtxt,
};
use index_vec::define_index_type;

define_index_type! {
    pub struct MirScopeIdx = u32;
}

impl MirScopeIdx {
    pub const ENTRY: Self = MirScopeIdx { _raw: 0 };
}

#[derive(Debug, Copy, Clone)]
pub struct MirScopedBranch {
    pub scope: MirScopeIdx,
    pub entry: MirBlockIdx,
}

pub struct MirScopedBuilder<'a> {
    tcx: &'a TyCtxt,
    body: MirBody,
    scope_id_gen: MirScopeIdx,
    scope_stack: Vec<LowerScope>,
    live_locals: Vec<LiveLocal>,
}

struct LowerScope {
    /// The scope in the `MirScopedBuilder` to which this low-level builder scope corresponds.
    id: MirScopeIdx,

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

struct LiveLocal {
    drop_unwind_target: Option<MirBlockIdx>,
    idx: MirLocalIdx,
}

impl<'tcx> MirScopedBuilder<'tcx> {
    pub fn new(tcx: &'tcx TyCtxt, arg_count: u32) -> Self {
        let mut this = Self {
            tcx,
            body: MirBody::default(),
            scope_id_gen: MirScopeIdx::ENTRY + 1,
            scope_stack: Vec::new(),
            live_locals: Vec::new(),
        };

        this.body.arg_count = arg_count;

        let entry_bb = this.body.cfg.create_block();

        let root_unwind_bb = this
            .body
            .cfg
            .create_block_with_terminator(MirTerminator::UnwindResume);

        // N.B. we do not register the return value as a local like all function arguments because
        // we don't want to drop it before a `return`. The only time we want to drop that place is
        // when we panic out of the function.
        let retval_unwind_bb =
            this.body
                .cfg
                .create_block_with_terminator(MirTerminator::EnsureDropped {
                    place: MirPlace::new(tcx, MirLocalIdx::RETURN, []),
                    target: root_unwind_bb,
                    unwind: MirUnwindBehavior::DoublePanic,
                });

        this.body.entry = entry_bb;
        this.scope_stack.push(LowerScope {
            id: MirScopeIdx::ENTRY,
            first_live_local: 0,
            unwind_bb: retval_unwind_bb,
            entry_bb,
            curr_bb: Some(entry_bb),
            branch_bb: None,
        });

        this
    }

    pub fn finish(self) -> MirBody {
        assert!(self.scope_stack.is_empty());
        self.body
    }
}

// Branch management
impl MirScopedBuilder<'_> {
    fn expect_top_curr(&mut self, expected_top: MirScopeIdx) -> MirBlockIdx {
        let top = self.scope_stack.last_mut().expect("no active scope");
        assert_eq!(top.id, expected_top);
        assert!(
            top.branch_bb.is_none(),
            "cannot write code to a scope onto which branches are actively being pushed"
        );

        // Unwrap OK: only branching scopes may lack a successor
        top.curr_bb.unwrap()
    }

    fn pop_scope_stack(&mut self) {
        let top = self.scope_stack.pop().unwrap();
        self.live_locals.truncate(top.first_live_local as usize);
    }

    pub fn begin_branch(&mut self, expected_top: MirScopeIdx) {
        let curr_bb = self.expect_top_curr(expected_top);

        let top = self.scope_stack.last_mut().unwrap();
        top.curr_bb = None;
        top.branch_bb = Some(curr_bb);
    }

    #[must_use]
    pub fn add_branch_scope(&mut self, expected_top: MirScopeIdx) -> MirScopedBranch {
        let top = self.scope_stack.last().expect("no active scope");
        assert_eq!(top.id, expected_top);
        assert!(
            top.branch_bb.is_some(),
            "must call `begin_branch` before `add_branch_scope`"
        );

        let sub_entry = self.body.cfg.create_block();
        let sub_id = self.scope_id_gen;
        self.scope_id_gen += 1;

        self.scope_stack.push(LowerScope {
            id: sub_id,
            first_live_local: self.live_locals.len() as u32,
            unwind_bb: top.unwind_bb,
            entry_bb: sub_entry,
            curr_bb: Some(sub_entry),
            branch_bb: None,
        });

        MirScopedBranch {
            scope: sub_id,
            entry: sub_entry,
        }
    }

    #[must_use]
    pub fn end_branch(
        &mut self,
        expected_top: MirScopeIdx,
        terminator: MirTerminator,
    ) -> Divergence {
        let top = self.scope_stack.last_mut().expect("no active scope");
        assert_eq!(top.id, expected_top);

        let branch_bb = top
            .branch_bb
            .take()
            .expect("must call `begin_branch` before `end_branch`");

        self.body.cfg.init_terminator(branch_bb, terminator);

        if top.curr_bb.is_some() {
            Divergence::MayDiverge
        } else {
            self.pop_scope_stack();
            Divergence::MustDiverge
        }
    }
}

// Code pushing
impl MirScopedBuilder<'_> {
    pub fn finish_unreachable(&mut self, expected_top: MirScopeIdx) {
        let block = self.expect_top_curr(expected_top);
        self.body
            .cfg
            .init_terminator(block, MirTerminator::Unreachable);

        self.pop_scope_stack();
    }

    pub fn finish_break(&mut self, expected_top: MirScopeIdx, target: MirScopeIdx) {
        self.finish_break_common(expected_top, target, false);
    }

    pub fn finish_continue(&mut self, expected_top: MirScopeIdx, target: MirScopeIdx) {
        self.finish_break_common(expected_top, target, true);
    }

    fn finish_break_common(
        &mut self,
        expected_top: MirScopeIdx,
        target: MirScopeIdx,
        is_continue: bool,
    ) {
        let mut curr_bb = self.expect_top_curr(expected_top);

        let mut scope_iter = self.scope_stack.iter_mut().rev();
        let mut local_iter = self.live_locals.iter().enumerate().rev().peekable();

        while let Some(top) = scope_iter.next() {
            let top = &*top;

            // Push drops.
            while let Some(&(live_local_idx, _)) = local_iter.peek()
                && live_local_idx as u32 >= top.first_live_local
            {
                let (_, local) = local_iter.next().unwrap();

                if let Some(unwind_if_drop_fails) = local.drop_unwind_target {
                    let successor = self.body.cfg.create_block();

                    self.body.cfg.init_terminator(
                        curr_bb,
                        MirTerminator::EnsureDropped {
                            place: MirPlace::new(self.tcx, local.idx, []),
                            target: successor,
                            unwind: MirUnwindBehavior::Continue(unwind_if_drop_fails),
                        },
                    );

                    curr_bb = successor;
                }

                self.body.cfg.push_stmt(
                    curr_bb,
                    MirStmt {
                        source_info: MirStmtSourceInfo::Break,
                        kind: MirStmtKind::StorageDead(local.idx),
                    },
                );
            }

            // If we've reached our target block, initialize the terminator.
            if top.id != target {
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

                        self.body
                            .cfg
                            .init_terminator(curr_bb, MirTerminator::Goto(spacer_block));

                        curr_bb = spacer_block;
                    }

                    self.body
                        .cfg
                        .init_terminator(curr_bb, MirTerminator::Goto(next_bb));
                }
                false => {
                    // This is a `break`. Jump to our parent's successor or return from the body.
                    match scope_iter.next() {
                        Some(successor) => {
                            let next_bb = *successor
                                .curr_bb
                                .get_or_insert_with(|| self.body.cfg.create_block());

                            self.body
                                .cfg
                                .init_terminator(curr_bb, MirTerminator::Goto(next_bb));
                        }
                        None => {
                            self.body
                                .cfg
                                .init_terminator(curr_bb, MirTerminator::Return);
                        }
                    }
                }
            }

            self.pop_scope_stack();
            return;
        }

        unreachable!("must break to ancestor");
    }

    pub fn push_local(
        &mut self,
        expected_top: MirScopeIdx,
        local: MirLocalIdx,
        can_omit_drop: bool,
    ) {
        let curr = self.expect_top_curr(expected_top);

        match can_omit_drop {
            true => {
                self.live_locals.push(LiveLocal {
                    drop_unwind_target: None,
                    idx: local,
                });
            }
            false => {
                let top = self.scope_stack.last_mut().unwrap();

                self.live_locals.push(LiveLocal {
                    drop_unwind_target: Some(top.unwind_bb),
                    idx: local,
                });

                top.unwind_bb =
                    self.body
                        .cfg
                        .create_block_with_terminator(MirTerminator::EnsureDropped {
                            place: MirPlace::new(self.tcx, local, []),
                            target: top.unwind_bb,
                            unwind: MirUnwindBehavior::DoublePanic,
                        });
            }
        }

        self.body.cfg.push_stmt(
            curr,
            MirStmt {
                source_info: MirStmtSourceInfo::Local,
                kind: MirStmtKind::StorageLive(local),
            },
        );
    }

    pub fn push_stmt(&mut self, expected_top: MirScopeIdx, stmt: MirStmt) {
        let curr = self.expect_top_curr(expected_top);

        self.body.cfg.push_stmt(curr, stmt);
    }

    pub fn push_unwind_terminator(
        &mut self,
        expected_top: MirScopeIdx,
        f: impl FnOnce(MirBlockIdx, MirUnwindBehavior) -> MirTerminator,
    ) {
        let curr = self.expect_top_curr(expected_top);
        let top = self.scope_stack.last_mut().unwrap();

        let successor = self.body.cfg.create_block();
        let terminator = f(successor, MirUnwindBehavior::Continue(top.unwind_bb));
        self.body.cfg.init_terminator(curr, terminator);

        top.curr_bb = Some(successor);
    }
}
