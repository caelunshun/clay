use crate::{
    base::{
        Session,
        arena::{HasListInterner as _, Obj},
    },
    semantic::{
        analysis::{
            borrowck::build::scope::{MirBuilderScopeIdx, MirScopedBuilder},
            sigck::CrateSigckVisitor,
        },
        syntax::{
            FnDef, MirAssignRvalue, MirLocalIdx, MirOperand, MirPlace, MirPlaceElem, MirStmt,
            MirStmtKind, MirStmtSourceInfo, SigTy, ThirBlock, ThirExpr, ThirExprKind, ThirLocal,
            ThirPat, ThirPatKind, ThirStmt, TyCtxt,
        },
    },
    utils::hash::FxHashMap,
};

// === Driver === //

pub fn build_function_mir(cx: &mut CrateSigckVisitor, def: Obj<FnDef>) {
    let s = cx.session();
    let tcx = cx.tcx();

    let Some(thir) = *def.r(s).thir_body else {
        return;
    };

    let mut builder = MirFromThirCtx::new(tcx, def);
    let rv = builder.lower_expr_rvalue(MirBuilderScopeIdx::ENTRY, thir);
    // TODO
}

// === Context === //

pub struct MirFromThirCtx<'tcx> {
    pub tcx: &'tcx TyCtxt,
    pub def: Obj<FnDef>,
    pub builder: MirScopedBuilder,
    pub labelled_scopes: FxHashMap<Obj<ThirExpr>, LabelledScope>,
    pub thir_locals: FxHashMap<Obj<ThirLocal>, MirLocalIdx>,
}

#[derive(Debug, Clone)]
pub enum MirRvalueOrPlace {
    Rvalue(MirAssignRvalue),
    Place(MirPlace),
}

#[derive(Copy, Clone)]
pub struct LabelledScope {
    pub scope: MirBuilderScopeIdx,
    pub out_place: Option<MirPlace>,
}

impl<'tcx> MirFromThirCtx<'tcx> {
    pub fn new(tcx: &'tcx TyCtxt, def: Obj<FnDef>) -> Self {
        Self {
            tcx,
            def,
            builder: MirScopedBuilder::default(),
            labelled_scopes: FxHashMap::default(),
            thir_locals: FxHashMap::default(),
        }
    }

    pub fn tcx(&self) -> &'tcx TyCtxt {
        self.tcx
    }

    pub fn session(&self) -> &'tcx Session {
        &self.tcx.session
    }

    pub fn lower_expr_rvalue(
        &mut self,
        scope: MirBuilderScopeIdx,
        expr: Obj<ThirExpr>,
    ) -> MirAssignRvalue {
        match self.lower_expr_preferred(scope, expr, None) {
            MirRvalueOrPlace::Rvalue(rvalue) => rvalue,
            MirRvalueOrPlace::Place(place) => MirAssignRvalue::Use(MirOperand::Move(place)),
        }
    }

    pub fn lower_expr_place(
        &mut self,
        scope: MirBuilderScopeIdx,
        expr: Obj<ThirExpr>,
        mut assign_into: Option<MirPlace>,
    ) -> MirPlace {
        let s = self.session();

        match self.lower_expr_preferred(scope, expr, assign_into) {
            MirRvalueOrPlace::Rvalue(rvalue) => {
                let assign_into =
                    self.create_assign_into_place_if_needed(scope, &mut assign_into, expr.r(s).ty);

                self.builder.push_statement(
                    scope,
                    MirStmt {
                        span: MirStmtSourceInfo::Simple(expr.r(s).span),
                        kind: MirStmtKind::Assign(Box::new((assign_into, rvalue))),
                    },
                );

                assign_into
            }
            MirRvalueOrPlace::Place(original_output) => {
                if let Some(assign_into) = assign_into
                    && original_output != assign_into
                {
                    self.builder.push_statement(
                        scope,
                        MirStmt {
                            span: MirStmtSourceInfo::Simple(expr.r(s).span),
                            kind: MirStmtKind::Assign(Box::new((
                                assign_into,
                                MirAssignRvalue::Use(MirOperand::Move(original_output)),
                            ))),
                        },
                    );
                }

                assign_into.unwrap_or(original_output)
            }
        }
    }

    pub fn lower_expr_preferred(
        &mut self,
        scope: MirBuilderScopeIdx,
        expr: Obj<ThirExpr>,
        mut assign_into: Option<MirPlace>,
    ) -> MirRvalueOrPlace {
        let tcx = self.tcx();
        let s = self.session();

        match *expr.r(s).kind {
            ThirExprKind::CreateZst => MirRvalueOrPlace::Rvalue(MirAssignRvalue::Zst(expr.r(s).ty)),
            ThirExprKind::CreateLiteral(lit) => {
                MirRvalueOrPlace::Rvalue(MirAssignRvalue::Literal(expr.r(s).ty, lit))
            }
            ThirExprKind::CreateArray(obj) => todo!(),
            ThirExprKind::CreateTuple(elems) => {
                let assign_into =
                    self.create_assign_into_place_if_needed(scope, &mut assign_into, expr.r(s).ty);

                for (idx, &elem) in elems.r(s).iter().enumerate() {
                    self.lower_expr_place(
                        scope,
                        elem,
                        Some(assign_into.extend(tcx, [MirPlaceElem::Field(idx as u32)])),
                    );
                }

                MirRvalueOrPlace::Place(assign_into)
            }
            ThirExprKind::PrimitiveBinOp(op, lhs, rhs) => {
                MirRvalueOrPlace::Rvalue(MirAssignRvalue::BinaryOp(
                    op,
                    Box::new((
                        MirOperand::Move(self.lower_expr_place(scope, lhs, None)),
                        MirOperand::Move(self.lower_expr_place(scope, rhs, None)),
                    )),
                ))
            }
            ThirExprKind::PrimitiveUnOp(op, lhs) => {
                MirRvalueOrPlace::Rvalue(MirAssignRvalue::UnaryOp(
                    op,
                    MirOperand::Move(self.lower_expr_place(scope, lhs, None)),
                ))
            }
            ThirExprKind::NoOp(expr) => self.lower_expr_preferred(scope, expr, assign_into),
            ThirExprKind::Break(label, value) => todo!(),
            ThirExprKind::Continue(label) => todo!(),
            ThirExprKind::Return(obj) => todo!(),
            ThirExprKind::Assign(lhs, rhs) => todo!(),
            ThirExprKind::Block(block) => {
                let assign_into =
                    self.create_assign_into_place_if_needed(scope, &mut assign_into, expr.r(s).ty);

                let scope = self.builder.push_scope(scope);

                self.labelled_scopes.insert(
                    expr,
                    LabelledScope {
                        scope,
                        out_place: Some(assign_into),
                    },
                );

                self.lower_block(scope, block, Some(assign_into));

                MirRvalueOrPlace::Place(assign_into)
            }
            ThirExprKind::Loop(obj) => todo!(),
            ThirExprKind::AddrOf(mutability, obj) => todo!(),
            ThirExprKind::Call(obj, obj1) => todo!(),
            ThirExprKind::Field(target, idx) => MirRvalueOrPlace::Place(
                self.lower_expr_place(scope, expr, None)
                    .extend(tcx, [MirPlaceElem::Field(idx)]),
            ),
            ThirExprKind::CreateBracedAdt { ctor, fields, rest } => {
                todo!()
            }
            ThirExprKind::Local(local) => {
                MirRvalueOrPlace::Place(MirPlace::new(tcx, self.thir_locals[&local], []))
            }
            ThirExprKind::If {
                cond,
                truthy,
                falsy,
            } => todo!(),
            ThirExprKind::DynUse(dyn_site_idx, obj) => todo!(),
            ThirExprKind::Match(obj, obj1) => todo!(),
            ThirExprKind::While(cond, block) => todo!(),
            ThirExprKind::Let(obj, obj1) => todo!(),
            ThirExprKind::Error(error) => MirRvalueOrPlace::Rvalue(MirAssignRvalue::Error(error)),
        }
    }

    pub fn lower_block(
        &mut self,
        scope: MirBuilderScopeIdx,
        expr: Obj<ThirBlock>,
        mut assign_into: Option<MirPlace>,
    ) {
        let s = self.session();

        for &stmt in &expr.r(s).stmts {
            match stmt {
                ThirStmt::Expr(expr) => {
                    let scope = self.builder.push_scope(scope);
                    let rvalue = self.lower_expr_rvalue(scope, expr);

                    self.builder.push_statement(
                        scope,
                        MirStmt {
                            span: MirStmtSourceInfo::Simple(expr.r(s).span),
                            kind: MirStmtKind::Discard(rvalue),
                        },
                    );
                }
                ThirStmt::Let(stmt) => {
                    todo!()
                }
            }
        }

        // TODO
    }

    pub fn lower_pat(
        &mut self,
        local_scope: MirBuilderScopeIdx,
        accept_scope: MirBuilderScopeIdx,
        reject_scope: MirBuilderScopeIdx,
        pat: Obj<ThirPat>,
        scrutinee: MirPlace,
    ) {
        let tcx = self.tcx();
        let s = self.session();

        match *pat.r(s).kind {
            ThirPatKind::Hole => {
                // (trivially accepted)
            }
            ThirPatKind::Binding {
                by_ref,
                local,
                and_bind,
            } => {
                let mir_local = self.builder.push_local(local_scope, local.r(s).ty);

                self.thir_locals.insert(local, mir_local);

                self.builder.push_statement(
                    reject_scope,
                    MirStmt {
                        span: MirStmtSourceInfo::Simple(pat.r(s).span),
                        kind: MirStmtKind::Assign(Box::new((
                            MirPlace::new(tcx, mir_local, []),
                            match by_ref {
                                Some(muta) => MirAssignRvalue::Ref(muta, scrutinee),
                                None => MirAssignRvalue::Use(MirOperand::Move(scrutinee)),
                            },
                        ))),
                    },
                );

                if let Some(and_bind) = and_bind {
                    self.lower_pat(local_scope, accept_scope, reject_scope, and_bind, scrutinee);
                }
            }
            ThirPatKind::Deref(pat) => {
                self.lower_pat(
                    local_scope,
                    accept_scope,
                    reject_scope,
                    pat,
                    scrutinee.extend(tcx, [MirPlaceElem::DerefPtr]),
                );
            }
            ThirPatKind::Or(obj) => todo!(),
            ThirPatKind::Slice(pat_list_front_and_tail) => todo!(),
            ThirPatKind::Tuple(pat_list_front_and_tail) => todo!(),
            ThirPatKind::Adt(obj, obj1) => todo!(),
            ThirPatKind::Error(_error) => {
                // (trivial)
            }
        }
    }

    pub fn create_assign_into_place_if_needed(
        &mut self,
        scope: MirBuilderScopeIdx,
        place: &mut Option<MirPlace>,
        ty: SigTy,
    ) -> MirPlace {
        let tcx = self.tcx();

        *place.get_or_insert_with(|| MirPlace {
            local: self.builder.push_local(scope, ty),
            projections: tcx.intern_list(&[]),
        })
    }
}
