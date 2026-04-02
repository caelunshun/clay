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

pub struct MirLowerCtxt<'tcx> {
    pub tcx: &'tcx TyCtxt,
    pub def: Obj<FnDef>,
    pub body: MirBody,
    pub locals: FxHashMap<Obj<FnLocal>, MirLocalIdx>,
}

impl<'tcx> MirLowerCtxt<'tcx> {
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

        let output = self.lower_rvalue(self.def.r(s).thir_body.unwrap(), &mut flow);

        flow.push_assign(
            &mut self.body,
            MirPlace {
                local: MirLocalIdx::RETURN,
                projections: tcx.intern_list(&[]),
            },
            output,
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
        let tcx = self.tcx();
        let s = self.session();

        match expr.r(s).kind {
            ThirExprKind::Local(local) => MirRvalueOrPlace::Place(self.lower_local(local)),
            ThirExprKind::CreatePathZst => MirRvalueOrPlace::Rvalue(MirAssignRvalue::Zst),
            ThirExprKind::CreateLiteral(lit) => {
                MirRvalueOrPlace::Rvalue(MirAssignRvalue::Literal(lit))
            }
            ThirExprKind::CreateTuple(args) => MirRvalueOrPlace::Rvalue(MirAssignRvalue::Tuple(
                self.lower_operand_list(args, flow),
            )),
            ThirExprKind::PrimitiveBinOp(op, lhs, rhs) => {
                MirRvalueOrPlace::Rvalue(MirAssignRvalue::BinaryOp(
                    op,
                    Box::new((self.lower_operand(lhs, flow), self.lower_operand(rhs, flow))),
                ))
            }
            ThirExprKind::PrimitiveUnOp(op, lhs) => MirRvalueOrPlace::Rvalue(
                MirAssignRvalue::UnaryOp(op, self.lower_operand(lhs, flow)),
            ),
            ThirExprKind::Return(ret_val) => {
                let value = self.lower_rvalue(ret_val, flow);

                flow.push_assign(
                    &mut self.body,
                    MirPlace {
                        local: MirLocalIdx::RETURN,
                        projections: tcx.intern_list(&[]),
                    },
                    value,
                );

                flow.push_return(&mut self.body);

                MirRvalueOrPlace::Rvalue(MirAssignRvalue::Tuple(Box::new([])))
            }
            ThirExprKind::Assign(lhs, rhs) => {
                let rhs = self.lower_place(rhs, flow);
                self.lower_pat(lhs, rhs, flow);

                MirRvalueOrPlace::Place(rhs)
            }
            ThirExprKind::Block(block) => {
                for &stmt in &block.r(s).stmts {
                    self.lower_stmt(stmt, flow);
                }

                if let Some(last_expr) = block.r(s).last_expr {
                    self.lower(last_expr, flow)
                } else {
                    MirRvalueOrPlace::Rvalue(MirAssignRvalue::Tuple(Box::new([])))
                }
            }
            ThirExprKind::Loop(block) => todo!(),
            ThirExprKind::AddrOf(muta, pointee) => MirRvalueOrPlace::Rvalue(MirAssignRvalue::Ref(
                muta,
                self.lower_place(pointee, flow),
            )),
            ThirExprKind::Call(callee, args) => {
                let callee = self.lower_operand(callee, flow);
                let args = self.lower_operand_list(args, flow);
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
                let cond = self.lower_place(cond, flow);

                let destination = MirPlace {
                    local: self.body.locals.push(MirLocal {}),
                    projections: tcx.intern_list(&[]),
                };

                let mut truthy_flow = MirLowerFlow::new(&mut self.body);
                let mut falsy_flow = MirLowerFlow::new(&mut self.body);

                let truthy_flow_entry = truthy_flow.curr(&mut self.body);
                let falsy_flow_entry = falsy_flow.curr(&mut self.body);

                flow.push_switch(
                    &mut self.body,
                    cond,
                    Box::new([truthy_flow_entry, falsy_flow_entry]),
                );

                let truthy_out_operand = self.lower_operand(truthy, &mut truthy_flow);
                if truthy_flow.is_continuing() {
                    truthy_flow.push_assign_use(&mut self.body, destination, truthy_out_operand);
                    truthy_flow.fallthrough_to(&mut self.body, flow);
                }

                if let Some(falsy) = falsy {
                    let falsy_out_operand = self.lower_operand(falsy, &mut falsy_flow);

                    if falsy_flow.is_continuing() {
                        falsy_flow.push_assign_use(&mut self.body, destination, falsy_out_operand);
                    }
                } else {
                    falsy_flow.push_assign(
                        &mut self.body,
                        destination,
                        MirAssignRvalue::Tuple(Box::new([])),
                    );
                }

                falsy_flow.fallthrough_to(&mut self.body, flow);

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
                let res = self.lower_operand(expr, flow);
                flow.push_discard(&mut self.body, res);
            }
            ThirStmt::Let(stmt) => {
                // TODO: divergent patterns
                if let Some(init) = stmt.r(s).init {
                    let rhs = self.lower_place(init, flow);
                    self.lower_pat(stmt.r(s).pat, rhs, flow);
                }
            }
        }
    }

    pub fn lower_rvalue(
        &mut self,
        expr: Obj<ThirExpr>,
        flow: &mut MirLowerFlow,
    ) -> MirAssignRvalue {
        match self.lower(expr, flow) {
            MirRvalueOrPlace::Rvalue(rvalue) => rvalue,
            MirRvalueOrPlace::Place(place) => {
                MirAssignRvalue::Use(self.convert_place_to_operand(place))
            }
        }
    }

    pub fn lower_place(&mut self, expr: Obj<ThirExpr>, flow: &mut MirLowerFlow) -> MirPlace {
        let tcx = self.tcx();

        let rvalue = match self.lower(expr, flow) {
            MirRvalueOrPlace::Rvalue(rvalue) => rvalue,
            MirRvalueOrPlace::Place(place) => return place,
        };

        let destination = MirPlace {
            local: self.body.locals.push(MirLocal {}),
            projections: tcx.intern_list(&[]),
        };

        if flow.is_continuing() {
            flow.push_assign(&mut self.body, destination, rvalue);
        }

        destination
    }

    pub fn lower_operand(&mut self, expr: Obj<ThirExpr>, flow: &mut MirLowerFlow) -> MirOperand {
        let place = self.lower_place(expr, flow);
        self.convert_place_to_operand(place)
    }

    pub fn lower_operand_list(
        &mut self,
        args: Obj<[Obj<ThirExpr>]>,
        flow: &mut MirLowerFlow,
    ) -> Box<[MirOperand]> {
        let s = self.session();

        args.r(s)
            .iter()
            .map(|&arg| self.lower_operand(arg, flow))
            .collect()
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
                flow.push_assign(&mut self.body, local, rvalue);

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
                let lhs = self.lower_place(lhs, flow);
                let rhs = self.convert_place_to_operand(rhs);
                flow.push_assign(&mut self.body, lhs, MirAssignRvalue::Use(rhs));
            }
            ThirPatKind::Error(_) => unreachable!(),
        }
    }

    pub fn convert_place_to_operand(&mut self, place: MirPlace) -> MirOperand {
        // TODO
        MirOperand::Move(place)
    }
}

#[derive(Debug, Clone)]
pub enum MirRvalueOrPlace {
    Rvalue(MirAssignRvalue),
    Place(MirPlace),
}
