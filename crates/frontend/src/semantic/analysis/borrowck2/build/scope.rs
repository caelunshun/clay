use crate::semantic::syntax::{
    MirBlock, MirBlockIdx, MirBody, MirLocal, MirLocalIdx, MirOperand, MirStmt, MirStmtKind,
    MirStmtSourceInfo, MirTerminator, SigTy,
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

pub struct MirScopedBuilder {
    scopes: IndexVec<MirBuilderScopeIdx, Scope>,
    body: MirBody,
}

struct Scope {
    parent: Option<ScopeParent>,
    locals: Vec<MirLocalIdx>,
    first_block: MirBlockIdx,
    curr_block: MirBlockIdx,
}

#[derive(Copy, Clone)]
struct ScopeParent {
    target: MirBuilderScopeIdx,
    returns_to: MirBlockIdx,
    last_local: usize,
}

impl Default for MirScopedBuilder {
    fn default() -> Self {
        let mut builder = Self {
            scopes: IndexVec::new(),
            body: MirBody::default(),
        };

        let entry_block = builder.body.blocks.push(MirBlock::default());

        assert_eq!(
            builder.scopes.push(Scope {
                parent: None,
                locals: Vec::new(),
                first_block: entry_block,
                curr_block: entry_block,
            }),
            MirBuilderScopeIdx::BOOTSTRAP_ENTRY
        );

        assert_eq!(
            builder.push_scope(MirBuilderScopeIdx::BOOTSTRAP_ENTRY),
            MirBuilderScopeIdx::ENTRY
        );

        builder
    }
}

/// Machinery
impl MirScopedBuilder {
    /// Allocates a local in a scope, which is live for all descendant scopes.
    #[must_use]
    pub fn push_local(&mut self, scope: MirBuilderScopeIdx, ty: SigTy) -> MirLocalIdx {
        let local = self.body.locals.push(MirLocal { ty });

        self.scopes[scope].locals.push(local);
        self.push_statement(
            scope,
            MirStmt {
                span: MirStmtSourceInfo::Local,
                kind: MirStmtKind::StorageLive(local),
            },
        );

        local
    }

    /// Pushes a regular statement to a scope.
    fn push_statement(&mut self, scope: MirBuilderScopeIdx, stmt: MirStmt) {
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
        let returns_to = self.body.blocks.push(MirBlock::default());
        self.scopes[scope].curr_block = returns_to;

        let successors = (0..succ_count)
            .map(|_| {
                let first_block = self.body.blocks.push(MirBlock::default());
                self.body.blocks[first_block]
                    .predecessors
                    .push(branching_block);

                self.scopes.push(Scope {
                    parent: Some(ScopeParent {
                        target: scope,
                        returns_to,
                        last_local: self.scopes[scope].locals.len(),
                    }),
                    locals: Vec::new(),
                    first_block,
                    curr_block: first_block,
                })
            })
            .collect::<SmallVec<[MirBuilderScopeIdx; 2]>>();

        self.body.blocks[branching_block].terminator = f(&successors
            .iter()
            .map(|&scope| self.scopes[scope].first_block)
            .collect::<SmallVec<[MirBlockIdx; 2]>>());

        successors
    }

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

                self.push_statement(
                    scope,
                    MirStmt {
                        span: MirStmtSourceInfo::Break,
                        kind: MirStmtKind::StorageDead(local),
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
        let dead_block = self.body.blocks.push(MirBlock::default());
        self.scopes[scope].curr_block = dead_block;

        self.body.blocks[branching_block].terminator = MirTerminator::Goto(next_bb);
        self.body.blocks[next_bb].predecessors.push(branching_block);
    }

    /// Finishes the current scope by breaking out to a target which must be an ancestor scope.
    pub fn push_break(&mut self, scope: MirBuilderScopeIdx, target: MirBuilderScopeIdx) {
        self.push_break_shared(scope, target, self.scopes[scope].parent.unwrap().returns_to);
    }

    /// Finishes the current scope by jumping back to the start of an ancestor scope.
    pub fn push_continue(&mut self, scope: MirBuilderScopeIdx, target: MirBuilderScopeIdx) {
        self.push_break_shared(scope, target, self.scopes[scope].first_block);
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
        // TODO

        self.body
    }
}

/// Wrappers
impl MirScopedBuilder {
    #[must_use]
    pub fn push_scope(&mut self, scope: MirBuilderScopeIdx) -> MirBuilderScopeIdx {
        let [sub_scope] = self.push_branch_fixed(scope, |[target]| MirTerminator::Goto(target));
        sub_scope
    }

    #[must_use]
    pub fn push_switch_dyn<const N: usize>(
        &mut self,
        scope: MirBuilderScopeIdx,
        scrutinee: MirOperand,
        constants: &[u64],
    ) -> SmallVec<[MirBuilderScopeIdx; 2]> {
        todo!()
    }

    #[must_use]
    pub fn push_switch_fixed<const N: usize>(
        &mut self,
        scope: MirBuilderScopeIdx,
        scrutinee: MirOperand,
        constants: [u64; N],
    ) -> [MirBuilderScopeIdx; N] {
        todo!()
    }

    pub fn push_return(&mut self, scope: MirBuilderScopeIdx) {
        self.push_break(scope, MirBuilderScopeIdx::ENTRY);
    }
}
