use crate::{
    base::{
        Session,
        arena::{HasListInterner, Obj},
    },
    semantic::{
        analysis::{MirLowerFlow, TyCtxt},
        syntax::{
            FnDef, FnLocal, MirAssignRvalue, MirBody, MirLocal, MirLocalIdx, MirOperand, MirPlace,
            MirPlaceElem, ThirExpr, ThirExprKind, ThirPat, ThirPatKind, ThirStmt,
        },
    },
    utils::hash::FxHashMap,
};
use index_vec::IndexVec;

pub struct MirBuildCtxt<'tcx> {
    pub tcx: &'tcx TyCtxt,
    pub def: Obj<FnDef>,
    pub body: MirBody,
    pub locals: FxHashMap<Obj<FnLocal>, MirLocalIdx>,
}

#[derive(Debug, Clone)]
pub enum MirRvalueOrPlace {
    Rvalue(MirAssignRvalue),
    Place(MirPlace),
    Unreachable,
}

impl<'tcx> MirBuildCtxt<'tcx> {
    pub fn new(tcx: &'tcx TyCtxt, def: Obj<FnDef>) -> Self {
        let mut body = MirBody {
            locals: IndexVec::new(),
            blocks: IndexVec::new(),
        };
        let mut locals = FxHashMap::default();

        // Define return value
        body.locals.push(MirLocal {});

        // Define arguments
        // TODO

        Self {
            tcx,
            def,
            body,
            locals,
        }
    }

    pub fn tcx(&self) -> &'tcx TyCtxt {
        self.tcx
    }

    pub fn session(&self) -> &'tcx Session {
        &self.tcx.session
    }

    pub fn lower_entry(&mut self) {
        let s = self.session();
        let tcx = self.tcx();

        let mut flow = MirLowerFlow::new(&mut self.body);

        self.lower_assign(
            MirPlace {
                local: MirLocalIdx::RETURN,
                projections: tcx.intern_list(&[]),
            },
            self.def.r(s).thir_body.unwrap(),
            &mut flow,
        );
        flow.push_return(&mut self.body);
    }

    pub fn lower_local(&mut self, local: Obj<FnLocal>) -> MirPlace {
        let tcx = self.tcx();

        MirPlace {
            local: *self
                .locals
                .entry(local)
                .or_insert_with(|| self.body.locals.push(MirLocal {})),
            projections: tcx.intern_list(&[]),
        }
    }

    pub fn lower(&mut self, expr: Obj<ThirExpr>, flow: &mut MirLowerFlow) -> MirRvalueOrPlace {
        if flow.is_finished() {
            return MirRvalueOrPlace::Unreachable;
        }

        let rv = self.lower_inner(expr, flow);

        if matches!(rv, MirRvalueOrPlace::Unreachable) {
            assert!(flow.is_finished());
        } else if flow.is_finished() {
            return MirRvalueOrPlace::Unreachable;
        }

        rv
    }

    fn lower_inner(&mut self, expr: Obj<ThirExpr>, flow: &mut MirLowerFlow) -> MirRvalueOrPlace {
        let tcx = self.tcx();
        let s = self.session();

        match expr.r(s).kind {
            ThirExprKind::Local(local) => MirRvalueOrPlace::Place(self.lower_local(local)),
            ThirExprKind::CreatePathZst => MirRvalueOrPlace::Rvalue(MirAssignRvalue::Zst),
            ThirExprKind::CreateLiteral(lit) => {
                MirRvalueOrPlace::Rvalue(MirAssignRvalue::Literal(lit))
            }
            ThirExprKind::CreateTuple(args) => {
                let Some(args) = self.lower_operand_list(args, flow) else {
                    return MirRvalueOrPlace::Unreachable;
                };

                MirRvalueOrPlace::Rvalue(MirAssignRvalue::Tuple(args))
            }
            ThirExprKind::PrimitiveBinOp(op, lhs, rhs) => {
                let (Some(lhs), Some(rhs)) =
                    (self.lower_operand(lhs, flow), self.lower_operand(rhs, flow))
                else {
                    return MirRvalueOrPlace::Unreachable;
                };

                MirRvalueOrPlace::Rvalue(MirAssignRvalue::BinaryOp(op, Box::new((lhs, rhs))))
            }
            ThirExprKind::PrimitiveUnOp(op, lhs) => {
                let Some(lhs) = self.lower_operand(lhs, flow) else {
                    return MirRvalueOrPlace::Unreachable;
                };

                MirRvalueOrPlace::Rvalue(MirAssignRvalue::UnaryOp(op, lhs))
            }
            ThirExprKind::Return(ret_val) => {
                self.lower_assign(
                    MirPlace {
                        local: MirLocalIdx::RETURN,
                        projections: tcx.intern_list(&[]),
                    },
                    ret_val,
                    flow,
                );

                flow.push_return(&mut self.body);

                MirRvalueOrPlace::Unreachable
            }
            ThirExprKind::Assign(lhs, rhs) => {
                let Some(rhs) = self.lower_place(rhs, flow) else {
                    return MirRvalueOrPlace::Unreachable;
                };

                self.lower_pat(lhs, rhs, flow);

                MirRvalueOrPlace::Rvalue(MirAssignRvalue::Tuple(Box::new([])))
            }
            ThirExprKind::Block(block) => {
                for &stmt in &block.r(s).stmts {
                    self.lower_stmt(stmt, flow);

                    if flow.is_finished() {
                        return MirRvalueOrPlace::Unreachable;
                    }
                }

                if let Some(last_expr) = block.r(s).last_expr {
                    self.lower(last_expr, flow)
                } else {
                    MirRvalueOrPlace::Rvalue(MirAssignRvalue::Tuple(Box::new([])))
                }
            }
            ThirExprKind::Loop(block) => todo!(),
            ThirExprKind::AddrOf(muta, pointee) => {
                let Some(pointee) = self.lower_place(pointee, flow) else {
                    return MirRvalueOrPlace::Unreachable;
                };

                MirRvalueOrPlace::Rvalue(MirAssignRvalue::Ref(muta, pointee))
            }
            ThirExprKind::Call(callee, args) => {
                let (Some(callee), Some(args)) = (
                    self.lower_operand(callee, flow),
                    self.lower_operand_list(args, flow),
                ) else {
                    return MirRvalueOrPlace::Unreachable;
                };

                let destination = MirPlace {
                    local: self.body.locals.push(MirLocal {}),
                    projections: tcx.intern_list(&[]),
                };

                flow.push_call(&mut self.body, callee, args, destination);

                MirRvalueOrPlace::Place(destination)
            }
            ThirExprKind::If {
                cond,
                truthy,
                falsy,
            } => {
                let Some(cond) = self.lower_place(cond, flow) else {
                    return MirRvalueOrPlace::Unreachable;
                };

                let destination = MirPlace {
                    local: self.body.locals.push(MirLocal {}),
                    projections: tcx.intern_list(&[]),
                };

                // We don't want to create sub-flows unless we know we're reachable to avoid
                // pushing unreachable code to the MIR, which could cause analysis to report borrow
                // errors in normally ignored code. This assertion is safe because `lower`
                // early-returns if the provided flow is finished.
                assert!(flow.is_continuing());

                let mut truthy_flow = MirLowerFlow::new(&mut self.body);
                let mut falsy_flow = MirLowerFlow::new(&mut self.body);

                let truthy_flow_entry = truthy_flow.expect_curr();
                let falsy_flow_entry = falsy_flow.expect_curr();

                flow.push_switch(
                    &mut self.body,
                    cond,
                    Box::new([truthy_flow_entry, falsy_flow_entry]),
                );

                if let Some(truthy_out_operand) = self.lower_operand(truthy, &mut truthy_flow) {
                    truthy_flow.push_assign_use(
                        &mut self.body,
                        truthy.r(s).span,
                        destination,
                        truthy_out_operand,
                    );
                    truthy_flow.push_goto_flow(&mut self.body, flow);
                }

                if let Some(falsy) = falsy {
                    if let Some(falsy_out_operand) = self.lower_operand(falsy, &mut falsy_flow) {
                        falsy_flow.push_assign_use(
                            &mut self.body,
                            falsy.r(s).span,
                            destination,
                            falsy_out_operand,
                        );
                    }
                } else {
                    falsy_flow.push_assign(
                        &mut self.body,
                        expr.r(s).span,
                        destination,
                        MirAssignRvalue::Tuple(Box::new([])),
                    );
                }

                falsy_flow.push_goto_flow(&mut self.body, flow);

                MirRvalueOrPlace::Place(destination)
            }
            ThirExprKind::While(cond, block) => todo!(),
            ThirExprKind::Let(obj, obj1) => todo!(),
            ThirExprKind::Error(_) => unreachable!(),
        }
    }

    pub fn lower_stmt(&mut self, stmt: ThirStmt, flow: &mut MirLowerFlow) {
        let s = self.session();

        match stmt {
            ThirStmt::Expr(expr) => {
                let Some(res) = self.lower_operand(expr, flow) else {
                    return;
                };

                flow.push_discard(&mut self.body, expr.r(s).span, res);
            }
            ThirStmt::Let(stmt) => {
                // TODO: divergent patterns
                if let Some(init) = stmt.r(s).init {
                    let Some(rhs) = self.lower_place(init, flow) else {
                        return;
                    };

                    self.lower_pat(stmt.r(s).pat, rhs, flow);
                }
            }
        }
    }

    pub fn lower_rvalue(
        &mut self,
        expr: Obj<ThirExpr>,
        flow: &mut MirLowerFlow,
    ) -> Option<MirAssignRvalue> {
        match self.lower(expr, flow) {
            MirRvalueOrPlace::Rvalue(rvalue) => Some(rvalue),
            MirRvalueOrPlace::Place(place) => {
                Some(MirAssignRvalue::Use(self.convert_place_to_operand(place)))
            }
            MirRvalueOrPlace::Unreachable => None,
        }
    }

    pub fn lower_assign(&mut self, lhs: MirPlace, rhs: Obj<ThirExpr>, flow: &mut MirLowerFlow) {
        let s = self.session();
        let span = rhs.r(s).span;

        let Some(rhs) = self.lower_rvalue(rhs, flow) else {
            return;
        };

        flow.push_assign(&mut self.body, span, lhs, rhs);
    }

    pub fn lower_place(
        &mut self,
        expr: Obj<ThirExpr>,
        flow: &mut MirLowerFlow,
    ) -> Option<MirPlace> {
        let s = self.session();
        let tcx = self.tcx();

        let rvalue = match self.lower(expr, flow) {
            MirRvalueOrPlace::Rvalue(rvalue) => rvalue,
            MirRvalueOrPlace::Place(place) => return Some(place),
            MirRvalueOrPlace::Unreachable => return None,
        };

        let destination = MirPlace {
            local: self.body.locals.push(MirLocal {}),
            projections: tcx.intern_list(&[]),
        };

        flow.push_assign(&mut self.body, expr.r(s).span, destination, rvalue);

        Some(destination)
    }

    pub fn lower_operand(
        &mut self,
        expr: Obj<ThirExpr>,
        flow: &mut MirLowerFlow,
    ) -> Option<MirOperand> {
        self.lower_place(expr, flow)
            .map(|place| self.convert_place_to_operand(place))
    }

    pub fn lower_operand_list(
        &mut self,
        args: Obj<[Obj<ThirExpr>]>,
        flow: &mut MirLowerFlow,
    ) -> Option<Box<[MirOperand]>> {
        let s = self.session();

        let mut collector = Vec::with_capacity(args.r(s).len());

        for &arg in args.r(s) {
            let arg = self.lower_operand(arg, flow)?;
            collector.push(arg);
        }

        Some(collector.into())
    }

    pub fn lower_pat(&mut self, pat: Obj<ThirPat>, rhs: MirPlace, flow: &mut MirLowerFlow) {
        let s = self.session();
        let tcx = self.tcx();

        match pat.r(s).kind {
            ThirPatKind::Wild => {
                // (no assignment)
            }
            ThirPatKind::Binding {
                by_ref,
                local,
                and_bind,
            } => {
                let rvalue = match by_ref {
                    Some(muta) => MirAssignRvalue::Ref(muta, rhs),
                    None => MirAssignRvalue::Use(self.convert_place_to_operand(rhs)),
                };

                let local = self.lower_local(local);
                flow.push_assign(&mut self.body, pat.r(s).span, local, rvalue);

                if let Some(and_bind) = and_bind {
                    self.lower_pat(and_bind, rhs, flow);
                }
            }
            ThirPatKind::Deref(pat) => {
                self.lower_pat(
                    pat,
                    MirPlace {
                        local: rhs.local,
                        projections: tcx.intern_list(
                            &rhs.projections
                                .r(s)
                                .iter()
                                .copied()
                                .chain([MirPlaceElem::DerefPtr])
                                .collect::<Vec<_>>(),
                        ),
                    },
                    flow,
                );
            }
            ThirPatKind::Or(obj) => todo!(),
            ThirPatKind::Place(lhs) => {
                let Some(lhs) = self.lower_place(lhs, flow) else {
                    return;
                };

                let rhs = self.convert_place_to_operand(rhs);
                flow.push_assign(
                    &mut self.body,
                    pat.r(s).span,
                    lhs,
                    MirAssignRvalue::Use(rhs),
                );
            }
            ThirPatKind::Error(_) => unreachable!(),
        }
    }

    pub fn convert_place_to_operand(&mut self, place: MirPlace) -> MirOperand {
        // TODO
        MirOperand::Move(place)
    }
}
