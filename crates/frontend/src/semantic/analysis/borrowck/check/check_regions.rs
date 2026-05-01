use crate::{
    base::{
        Session,
        arena::{HasInterner, HasListInterner, Obj},
    },
    semantic::{
        analysis::{
            ClauseCx, ClauseImportEnvRef, ClauseOrigin, CrateBorrowCheckVisitor, HrtbUniverse,
            MirDataflowFacts, UnifyCxMode,
        },
        syntax::{
            FnDef, IntKind, MirAssignRvalue, MirBlock, MirBody, MirLocal, MirLocalIdx, MirOperand,
            MirPlace, MirPlaceElem, MirStmt, MirStmtKind, MirTerminator, Re, RelationDirection,
            RelationMode, SimpleTyKind, TraitParam, TraitSpec, Ty, TyCtxt, TyKind, TyOrRe,
            UniversalReVarSourceInfo,
        },
    },
};
use index_vec::{IndexSlice, IndexVec};

impl<'tcx> CrateBorrowCheckVisitor<'tcx> {
    pub fn borrow_check(&self, def: Obj<FnDef>, body: &MirBody, df: &MirDataflowFacts) {
        let tcx = self.tcx();

        let mut body = body.clone();

        let mut ccx = ClauseCx::new(tcx, self.coherence, self.krate, UnifyCxMode::RegionAware);

        let env = ccx.create_universal_env_for_fn_def(HrtbUniverse::ROOT_REF, def);

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

        BodyInstantiateCx {
            ccx: &mut ccx,
            env: env.as_ref(),
            local_universals: local_universals.as_slice(),
        }
        .visit_body(&mut body);

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

struct BodyInstantiateCx<'a, 'tcx> {
    ccx: &'a mut ClauseCx<'tcx>,
    env: ClauseImportEnvRef<'a>,
    local_universals: &'a IndexSlice<MirLocalIdx, [Re]>,
}

impl BodyInstantiateCx<'_, '_> {
    fn visit_body(&mut self, body: &mut MirBody) {
        for (local_idx, local) in body.locals.iter_mut_enumerated() {
            self.visit_local(local_idx, local);
        }

        for block in &mut body.blocks {
            self.visit_block(block);
        }
    }

    // Import all types within the body and ensure that they're well-formed. Additionally, local
    // types must outlive the universal region associated with that local.
    fn visit_local(&mut self, local_idx: MirLocalIdx, local: &mut MirLocal) {
        local.ty = self
            .ccx
            .import_report_elsewhere(&HrtbUniverse::ROOT, self.env, local.ty);

        self.ccx.oblige_ty_outlives_re(
            ClauseOrigin::empty_report(),
            local.ty,
            self.local_universals[local_idx],
            RelationDirection::LhsOntoRhs,
        );
    }

    fn visit_block(&mut self, block: &mut MirBlock) {
        for stmt in &mut block.stmts {
            self.visit_statement(stmt);
        }

        self.visit_terminator(&mut block.terminator);
    }

    fn visit_statement(&mut self, stmt: &mut MirStmt) {
        match &mut stmt.kind {
            MirStmtKind::Assign(assign) => {
                let (_lhs, rhs) = &mut **assign;
                self.visit_rvalue(rhs);
            }
            MirStmtKind::Discard(_) => {
                // (terminal)
            }
        }
    }

    fn visit_terminator(&mut self, terminator: &mut MirTerminator) {
        match terminator {
            MirTerminator::Goto(_)
            | MirTerminator::Call {
                callee: _,
                args: _,
                destination: _,
                target: _,
            }
            | MirTerminator::Drop {
                place: _,
                target: _,
            }
            | MirTerminator::Switch {
                scrutinee: _,
                targets: _,
            }
            | MirTerminator::Return
            | MirTerminator::Unreachable
            | MirTerminator::Placeholder => {
                // (terminal)
            }
        }
    }

    fn visit_rvalue(&mut self, rvalue: &mut MirAssignRvalue) {
        match rvalue {
            MirAssignRvalue::Tuple(_)
            | MirAssignRvalue::Use(_)
            | MirAssignRvalue::Ref(_, _)
            | MirAssignRvalue::BinaryOp(_, _)
            | MirAssignRvalue::UnaryOp(_, _)
            | MirAssignRvalue::Discriminant(_) => {
                // (no types)
            }
            MirAssignRvalue::Literal(_, _) => {
                // (ty is uninteresting)
            }
            MirAssignRvalue::Zst(ty) => {
                *ty = self
                    .ccx
                    .import_report_elsewhere(HrtbUniverse::ROOT_REF, self.env, *ty);
            }
        }
    }
}

struct RegionCheckCx<'a, 'tcx> {
    ccx: &'a mut ClauseCx<'tcx>,
    body: &'a MirBody,
    local_universals: &'a IndexVec<MirLocalIdx, Re>,
}

impl<'tcx> RegionCheckCx<'_, 'tcx> {
    fn session(&self) -> &'tcx Session {
        self.ccx.session()
    }

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
        let s = self.session();
        let tcx = self.tcx();

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
            MirTerminator::Switch {
                scrutinee: _,
                targets: _,
            } => {
                // (assumed valid)
            }
            MirTerminator::Call {
                callee,
                args,
                destination,
                target: _,
            } => {
                let callee = self.check_operand(*callee);
                let destination = self.check_place(*destination);
                let args = tcx.intern_list(
                    &args
                        .iter()
                        .map(|&arg| self.check_operand(arg))
                        .collect::<Vec<_>>(),
                );

                self.ccx.oblige_ty_meets_trait_instantiated(
                    ClauseOrigin::empty_report(),
                    HrtbUniverse::ROOT,
                    callee,
                    TraitSpec {
                        def: self.ccx.krate().r(s).lang_items.fn_once_trait().unwrap(),
                        params: tcx.intern_list(&[
                            TraitParam::Equals(TyOrRe::Ty(tcx.intern(TyKind::Tuple(args)))),
                            TraitParam::Equals(TyOrRe::Ty(destination)),
                        ]),
                    },
                );
            }
        }
    }

    fn check_place(&mut self, place: MirPlace) -> Ty {
        let s = self.session();
        let mut ty = self.body.locals[place.local].ty;

        for &projection in place.projections.r(s) {
            match projection {
                MirPlaceElem::DerefPtr => {
                    self.ccx.poll_obligations();

                    // We know we can't have an inference variable after `ClauseCx` progress because
                    // all types are known at every point.
                    let TyKind::Reference(_re, _muta, pointee) =
                        *self.ccx.peel_ty_infer_var_after_poll(ty).r(s)
                    else {
                        unreachable!()
                    };

                    ty = pointee;
                }
            }
        }

        ty
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
                let (lhs, rhs) = &**sides;

                let lhs = self.check_operand(*lhs);
                let rhs = self.check_operand(*rhs);

                self.ccx.oblige_ty_unifies_ty(
                    ClauseOrigin::never_printed(),
                    lhs,
                    rhs,
                    RelationMode::Equate,
                );

                lhs
            }
            MirAssignRvalue::UnaryOp(_op_kind, side) => self.check_operand(*side),
            MirAssignRvalue::Discriminant(_place) => {
                tcx.intern(TyKind::Simple(SimpleTyKind::Uint(IntKind::S32)))
            }
        }
    }
}
