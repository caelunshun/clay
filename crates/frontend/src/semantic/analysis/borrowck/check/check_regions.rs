use crate::{
    base::arena::{HasInterner, HasListInterner, Obj},
    semantic::{
        analysis::{
            ClauseCx, ClauseOrigin, CrateBorrowCheckVisitor, HrtbUniverse, MirDataflowFacts,
            TyCtxt, TyFolderInfallibleExt as _, TyVisitorInfallibleExt as _, UnifyCxMode,
        },
        syntax::{
            FnDef, IntKind, MirAssignRvalue, MirBody, MirLocalIdx, MirOperand, MirPlace, MirStmt,
            MirStmtKind, MirTerminator, Re, RelationDirection, RelationMode, SimpleTyKind, Ty,
            TyKind, UniversalReVarSourceInfo,
        },
    },
};
use index_vec::IndexVec;

impl<'tcx> CrateBorrowCheckVisitor<'tcx> {
    pub fn borrow_check(&self, def: Obj<FnDef>, body: &MirBody, df: &MirDataflowFacts) {
        let tcx = self.tcx();

        let mut body = body.clone();

        let mut ccx = ClauseCx::new(tcx, self.coherence, self.krate, UnifyCxMode::RegionAware);

        let env = ccx.import_fn_def_env_as_universal(
            &ClauseOrigin::never_printed(),
            HrtbUniverse::ROOT_REF,
            def,
        );

        // Give each local a universal region representing its lifetime within the function body.
        // We permit a given local to outlive another if `live(rhs)` implies `occupied(lhs)`—in
        // other words, whenever `rhs` is used by some later statement, `lhs` will contain a value
        // that can be accessed.
        let local_universals = body
            .locals
            .indices()
            .map(|idx| ccx.fresh_re_universal(UniversalReVarSourceInfo::MirLocal(idx)))
            .collect::<IndexVec<MirLocalIdx, Re>>();

        for (rhs_local, &rhs_re) in local_universals.iter_enumerated() {
            let lhs_outlive_mask = df.can_outlive_rhs_mask(&body, rhs_local);

            for lhs_local in lhs_outlive_mask.iter() {
                let lhs_re = local_universals[lhs_local];

                ccx.permit_universe_re_outlives_re(lhs_re, rhs_re, RelationDirection::LhsOntoRhs);
            }
        }

        // Import all types within the body and ensure that they're well-formed. Additionally, local
        // types must outlive the universal region associated with that local.
        for (local_idx, local) in body.locals.iter_mut_enumerated() {
            local.ty = ccx
                .importer(
                    &ClauseOrigin::empty_report(),
                    HrtbUniverse::ROOT,
                    env.as_ref(),
                )
                .fold(local.ty);

            ccx.wf_visitor(HrtbUniverse::ROOT).visit(local.ty);

            ccx.oblige_ty_outlives_re(
                ClauseOrigin::empty_report(),
                local.ty,
                local_universals[local_idx],
                RelationDirection::LhsOntoRhs,
            );
        }

        // TODO: Import

        // Type-check the MIR body to create obligations between regions.
        RegionCheckCx {
            ccx: &mut ccx,
            body: &body,
            local_universals: &local_universals,
        }
        .check_body();

        ccx.verify();
    }
}

pub struct RegionCheckCx<'a, 'tcx> {
    pub ccx: &'a mut ClauseCx<'tcx>,
    pub body: &'a MirBody,
    pub local_universals: &'a IndexVec<MirLocalIdx, Re>,
}

impl<'tcx> RegionCheckCx<'_, 'tcx> {
    fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    fn check_body(&mut self) {
        for block in self.body.blocks.iter() {
            for stmt in &block.stmts {
                self.check_stmt(stmt);
            }

            self.check_terminator(&block.terminator);
        }
    }

    fn check_stmt(&mut self, stmt: &MirStmt) {
        match &stmt.kind {
            MirStmtKind::Assign(stmt) => {
                let (lhs, rhs) = &**stmt;

                let lhs_ty = self.check_place(*lhs);
                let rhs_ty = self.check_rvalue(rhs);

                self.ccx.oblige_ty_unifies_ty(
                    ClauseOrigin::empty_report(),
                    rhs_ty,
                    lhs_ty,
                    RelationMode::LhsOntoRhs,
                );
            }
            MirStmtKind::Discard(_) => {
                // (ignored)
            }
        }
    }

    fn check_terminator(&mut self, terminator: &MirTerminator) {
        match terminator {
            MirTerminator::Goto(_)
            | MirTerminator::Return
            | MirTerminator::Unreachable
            | MirTerminator::Placeholder
            | MirTerminator::Drop {
                place: _,
                target: _,
            } => {
                // (empty)
            }
            MirTerminator::Call {
                callee,
                args,
                destination,
                target: _,
            } => {
                // TODO
            }
            MirTerminator::Switch {
                scrutinee,
                targets: _,
            } => {
                // TODO
            }
        }
    }

    fn check_place(&mut self, place: MirPlace) -> Ty {
        // TODO: projections
        self.body.locals[place.local].ty
    }

    fn check_operand(&mut self, operand: MirOperand) -> Ty {
        self.check_place(operand.place())
    }

    fn check_rvalue(&mut self, rvalue: &MirAssignRvalue) -> Ty {
        let tcx = self.tcx();

        match rvalue {
            MirAssignRvalue::Tuple(operands) => tcx.intern(TyKind::Tuple(
                tcx.intern_list(
                    &operands
                        .iter()
                        .map(|&operand| self.check_operand(operand))
                        .collect::<Vec<_>>(),
                ),
            )),
            MirAssignRvalue::Use(operand) => self.check_operand(*operand),
            MirAssignRvalue::Ref(muta, place) => {
                let pointee = self.check_place(*place);

                tcx.intern(TyKind::Reference(
                    self.local_universals[place.local],
                    *muta,
                    pointee,
                ))
            }
            MirAssignRvalue::Zst(ty) => *ty,
            MirAssignRvalue::Literal(ty, _lit) => *ty,
            MirAssignRvalue::BinaryOp(_op_kind, sides) => {
                todo!()
            }
            MirAssignRvalue::UnaryOp(_op_kind, side) => self.check_operand(*side),
            MirAssignRvalue::Discriminant(_place) => {
                tcx.intern(TyKind::Simple(SimpleTyKind::Uint(IntKind::S32)))
            }
        }
    }
}
