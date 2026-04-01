use crate::{
    base::{
        Session,
        arena::{HasListInterner, Obj},
    },
    semantic::{
        analysis::{MirLowerFlow, TyCtxt},
        syntax::{
            FnDef, MirAssignRvalue, MirBody, MirLocal, MirOperand, MirPlace, ThirExpr, ThirExprKind,
        },
    },
};
use index_vec::IndexVec;

pub struct MirLowerCtxt<'tcx> {
    pub tcx: &'tcx TyCtxt,
    pub def: Obj<FnDef>,
    pub body: MirBody,
}

impl<'tcx> MirLowerCtxt<'tcx> {
    pub fn new(tcx: &'tcx TyCtxt, def: Obj<FnDef>) -> Self {
        Self {
            tcx,
            def,
            body: MirBody {
                locals: IndexVec::new(),
                blocks: IndexVec::new(),
            },
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

        dbg!(*self.def.r(s).thir_body);
    }

    pub fn lower_rvalue(
        &mut self,
        expr: Obj<ThirExpr>,
        flow: &mut MirLowerFlow,
    ) -> MirAssignRvalue {
        let s = self.session();

        match expr.r(s).kind {
            ThirExprKind::AddrOf(mutability, pointee) => {
                MirAssignRvalue::Ref(mutability, self.lower_place(pointee, flow))
            }

            ThirExprKind::CreatePathZst => todo!(),
            ThirExprKind::CreateLiteral(ast_lit) => todo!(),
            ThirExprKind::CreateTuple(obj) => todo!(),
            ThirExprKind::PrimitiveBinOp(ast_bin_op_kind, obj, obj1) => todo!(),
            ThirExprKind::PrimitiveUnOp(ast_un_op_kind, obj) => todo!(),
            ThirExprKind::Return(obj) => todo!(),
            ThirExprKind::Assign(obj, obj1) => todo!(),
            ThirExprKind::Block(obj) => todo!(),
            ThirExprKind::Loop(obj) => todo!(),
            ThirExprKind::Call(obj, obj1) => todo!(),
            ThirExprKind::Local(obj) => todo!(),
            ThirExprKind::If {
                cond,
                truthy,
                falsy,
            } => todo!(),
            ThirExprKind::While(obj, obj1) => todo!(),
            ThirExprKind::Let(obj, obj1) => todo!(),
            ThirExprKind::Error(error_guaranteed) => todo!(),
        }
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

    pub fn lower_place(&mut self, expr: Obj<ThirExpr>, flow: &mut MirLowerFlow) -> MirPlace {
        let tcx = self.tcx();
        let s = self.session();

        match expr.r(s).kind {
            ThirExprKind::Local(local) => {
                todo!()
            }
            ThirExprKind::CreatePathZst => {
                todo!()
            }
            ThirExprKind::CreateLiteral(ast_lit) => todo!(),
            ThirExprKind::CreateTuple(obj) => todo!(),
            ThirExprKind::PrimitiveBinOp(ast_bin_op_kind, obj, obj1) => {
                todo!()
            }
            ThirExprKind::PrimitiveUnOp(ast_un_op_kind, obj) => todo!(),
            ThirExprKind::Return(obj) => todo!(),
            ThirExprKind::Assign(obj, obj1) => todo!(),
            ThirExprKind::Block(obj) => todo!(),
            ThirExprKind::Loop(obj) => todo!(),
            ThirExprKind::AddrOf(mutability, obj) => todo!(),
            ThirExprKind::Call(callee, args) => {
                let callee = self.lower_operand(callee, flow);
                let args = self.lower_operand_list(args, flow);
                let destination = MirPlace {
                    local: self.body.locals.push(MirLocal {}),
                    projections: tcx.intern_list(&[]),
                };

                flow.push_call(&mut self.body, callee, args, destination);

                destination
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

                let truthy_flow_entry = truthy_flow.expect_curr();
                let falsy_flow_entry = falsy_flow.expect_curr();

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
                }

                falsy_flow.fallthrough_to(&mut self.body, flow);

                destination
            }
            ThirExprKind::While(obj, obj1) => todo!(),
            ThirExprKind::Let(obj, obj1) => todo!(),
            ThirExprKind::Error(error_guaranteed) => todo!(),
        }
    }

    pub fn convert_place_to_operand(&mut self, place: MirPlace) -> MirOperand {
        todo!()
    }
}
