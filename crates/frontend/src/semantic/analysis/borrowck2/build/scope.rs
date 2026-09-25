use crate::semantic::syntax::{MirBlockIdx, MirLocalIdx, MirStmt, MirTerminator, SigTy, TyCtxt};
use index_vec::define_index_type;
use smallvec::SmallVec;

define_index_type! {
    pub struct MirBuilderScopeIdx = u32;
}

impl MirBuilderScopeIdx {
    pub const ENTRY: MirBuilderScopeIdx = MirBuilderScopeIdx { _raw: 0 };
}

pub struct MirScopedBuilder<'tcx> {
    tcx: &'tcx TyCtxt,
}

impl<'tcx> MirScopedBuilder<'tcx> {
    pub fn new(tcx: &'tcx TyCtxt) -> Self {
        todo!()
    }

    /// Allocates a local in a scope, which is live for all descendant scopes.
    pub fn push_local(&mut self, scope: MirBuilderScopeIdx, ty: SigTy) -> MirLocalIdx {
        todo!()
    }

    /// Pushes a regular statement to a scope.
    pub fn push_statement(&mut self, scope: MirBuilderScopeIdx, stmt: MirStmt) {
        todo!()
    }

    /// Pushes a terminator that branches into some number of child scopes. This can handle diverging
    /// terminators where the successor count is zero and unconditional scope entries where the
    /// successor count is one (e.g. `loop` entries) but cannot handle jumps out of the current
    /// scope, which must be done with [`Self::push_break`] and [`Self::push_continue`].
    pub fn push_branch(
        &mut self,
        scope: MirBuilderScopeIdx,
        succ_count: usize,
        f: impl FnOnce(SmallVec<[MirBlockIdx; 2]>) -> MirTerminator,
    ) -> SmallVec<[MirBuilderScopeIdx; 2]> {
        todo!()
    }

    /// Finishes the current scope by breaking out to a target which must be an ancestor scope.
    pub fn push_break(&mut self, scope: MirBuilderScopeIdx, target: MirBuilderScopeIdx) {
        todo!()
    }

    /// Finishes the current scope by jumping back to the start of an ancestor scope.
    pub fn push_continue(&mut self, scope: MirBuilderScopeIdx, target: MirBuilderScopeIdx) {
        todo!()
    }
}
