use crate::{
    base::{Session, arena::Obj},
    semantic::{
        analysis::{ClauseCx, CrateTypeckVisitor, TyCtxt, TyVisitor},
        syntax::{Block, Divergence, Expr, ExprKind, FnDef, Ty, TyAndDivergence, TyKind},
    },
};
use std::{convert::Infallible, ops::ControlFlow};

impl CrateTypeckVisitor<'_> {
    pub fn visit_fn_def(&mut self, def: Obj<FnDef>) -> ControlFlow<Infallible> {
        let s = self.session();

        // WF-check the signature.
        self.visit_generic_binder(def.r(s).generics)?;

        // TODO
        // if let Some(self_param) = *def.r(s).self_param {
        //     self.visit_spanned_ty(self_param)?;
        // }

        for arg in def.r(s).args.r(s) {
            self.visit_spanned_ty(arg.ty)?;
        }

        self.visit_spanned_ty(*def.r(s).ret_ty)?;

        // Check the body
        // TODO

        ControlFlow::Continue(())
    }
}

// === FuncCx === //

pub struct FuncCx<'tcx> {
    ccx: ClauseCx<'tcx>,
}

impl<'tcx> FuncCx<'tcx> {
    pub fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    pub fn session(&self) -> &'tcx Session {
        self.ccx.session()
    }

    pub fn check_expr(
        &mut self,
        exprs: impl IntoIterator<Item = Obj<Expr>>,
        demand: Option<Ty>,
    ) -> TyAndDivergence {
        todo!()
    }

    fn visit_expr(&mut self, expr: Obj<Expr>) -> TyAndDivergence {
        let s = self.session();
        let tcx = self.tcx();

        let mut divergence = Divergence::MayDiverge;

        let ty = match *expr.r(s).kind {
            ExprKind::Array(elems) => {
                let elem_ty = divergence.and_do(self.check_expr(elems.r(s).iter().copied(), None));

                _ = elem_ty;
                todo!();
            }
            ExprKind::Call(callee, args) => {
                let callee = divergence.and_do(self.check_expr([callee], None));

                match *self.ccx.peel_ty_var(callee).r(s) {
                    TyKind::FnDef(obj) => todo!(),
                    TyKind::Trait(intern) => todo!(),
                    TyKind::Error(err) => {
                        // Propagate error.
                        todo!();
                    }
                    TyKind::Simple(_)
                    | TyKind::Universal(_)
                    | TyKind::Tuple(_)
                    | TyKind::Reference(_, _, _)
                    | TyKind::Adt(_) => {
                        // Unsupported callee
                        todo!();
                    }
                    TyKind::InferVar(_) => {
                        // Type must be known
                        todo!();
                    }
                    TyKind::ExplicitInfer | TyKind::This => {
                        unreachable!()
                    }
                }
            }
            ExprKind::Method {
                callee,
                generics,
                args,
            } => todo!(),
            ExprKind::Tuple(obj) => todo!(),
            ExprKind::Binary(ast_bin_op_spanned, obj, obj1) => todo!(),
            ExprKind::Unary(ast_un_op_kind, obj) => todo!(),
            ExprKind::Literal(ast_lit) => todo!(),
            ExprKind::TupleOrUnitCtor(adt_ctor_instance) => todo!(),
            ExprKind::FnItemLit(obj, spanned) => todo!(),
            ExprKind::TypeRelative {
                self_ty,
                as_trait,
                assoc_name,
                assoc_args,
            } => todo!(),
            ExprKind::Cast(obj, spanned) => todo!(),
            ExprKind::If {
                cond,
                truthy,
                falsy,
            } => todo!(),
            ExprKind::While(obj, obj1) => todo!(),
            ExprKind::Let(obj, obj1) => todo!(),
            ExprKind::ForLoop { pat, iter, body } => todo!(),
            ExprKind::Loop(obj) => todo!(),
            ExprKind::Match(obj, obj1) => todo!(),
            ExprKind::Block(obj) => todo!(),
            ExprKind::Assign(obj, obj1) => todo!(),
            ExprKind::AssignOp(ast_assign_op_kind, obj, obj1) => todo!(),
            ExprKind::Field(obj, ident) => todo!(),
            ExprKind::GenericMethodCall {
                target,
                method,
                generics,
                args,
            } => todo!(),
            ExprKind::Index(obj, obj1) => todo!(),
            ExprKind::Range(range_expr) => todo!(),
            ExprKind::LocalSelf => todo!(),
            ExprKind::Local(obj) => todo!(),
            ExprKind::AddrOf(mutability, obj) => todo!(),
            ExprKind::Break { label, expr } => todo!(),
            ExprKind::Continue { label } => todo!(),
            ExprKind::Return(obj) => todo!(),
            ExprKind::Struct(struct_expr) => todo!(),
            ExprKind::Error(error_guaranteed) => todo!(),
        };

        TyAndDivergence { ty, divergence }
    }

    pub fn check_block(&mut self, block: Obj<Block>, demand: Option<Ty>) -> TyAndDivergence {
        todo!()
    }
}
