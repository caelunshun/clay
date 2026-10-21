use crate::semantic::{
    analysis::borrowck::scopes::{MirScopedBranch, RawMirScopedBuilder, TraitCache},
    syntax::{
        MirLocal, MirLocalIdx, MirOperand, MirPlace, MirRvalue, MirScopeIdx, MirSourceInfo,
        MirStmt, MirStmtKind, MirTerminator, MirTerminatorKind,
    },
};

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

    fn push_local(&mut self, in_scope: MirScopeIdx, local: MirLocal) -> MirLocalIdx {
        let can_omit_drop = self.trait_cache().can_omit_drop(local.ty);

        self.raw_builder()
            .push_local(in_scope, local, can_omit_drop)
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
