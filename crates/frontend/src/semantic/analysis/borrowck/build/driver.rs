use crate::{
    base::{
        Session,
        arena::{HasListInterner as _, Obj},
    },
    semantic::{
        analysis::borrowck::build::{MirBuilderScopeIdx, MirScopedBuilder},
        syntax::{
            FnDef, MirAssignRvalue, MirLocalIdx, MirOperand, MirPlace, MirPlaceElem, MirStmt,
            MirStmtKind, MirStmtSourceInfo, SigTy, ThirBlock, ThirExpr, ThirExprKind, ThirLocal,
            TyCtxt,
        },
    },
    utils::hash::FxHashMap,
};

pub struct MirFromThirCtx<'tcx> {
    pub tcx: &'tcx TyCtxt,
    pub def: Obj<FnDef>,
    pub builder: MirScopedBuilder,
    pub labelled_scopes: FxHashMap<Obj<ThirBlock>, LabelledScope>,
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
    pub loop_place: Option<MirPlace>,
}

impl<'tcx> MirFromThirCtx<'tcx> {
    pub fn new(tcx: &'tcx TyCtxt, def: Obj<FnDef>) -> Self {
        todo!()
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
            ThirExprKind::Block(block) => todo!(),
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
            ThirExprKind::Local(local) => MirRvalueOrPlace::Place(MirPlace {
                local: *self.thir_locals.get(&local).unwrap(),
                projections: tcx.intern_list(&[]),
            }),
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
