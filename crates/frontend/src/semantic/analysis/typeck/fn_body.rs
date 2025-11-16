use crate::{
    base::{Session, arena::Obj},
    semantic::{
        analysis::{InferCx, TyCtxt},
        syntax::{Block, Expr, ExprKind, FuncLocal, RelationMode, SpannedTy, TyKind},
    },
    utils::hash::FxHashMap,
};

pub struct FnCtxt<'tcx> {
    icx: InferCx<'tcx>,
    local_types: FxHashMap<Obj<FuncLocal>, SpannedTy>,
    pre_coerce_expr_types: FxHashMap<Obj<Expr>, SpannedTy>,
}

impl<'tcx> FnCtxt<'tcx> {
    pub fn session(&self) -> &'tcx Session {
        self.icx.session()
    }

    pub fn tcx(&self) -> &'tcx TyCtxt {
        self.icx.tcx()
    }

    fn check_block(&mut self, block: Obj<Block>) {
        let s = self.icx.session();

        for stmt in &block.r(s).stmts {}
    }

    fn check_expr_demand(&mut self, expr: Obj<Expr>, demand: SpannedTy) {
        let actual = self.check_expr(expr);

        let Err(err) = self
            .icx
            .relate_ty_and_ty(actual, demand, RelationMode::LhsOntoRhs)
        else {
            return;
        };

        // TODO
    }

    fn check_expr(&mut self, expr: Obj<Expr>) -> SpannedTy {
        let s = self.session();
        let tcx = self.tcx();

        let pre_coerce_expr_ty = match &expr.r(s).kind {
            ExprKind::Array(elems) => todo!(),
            ExprKind::Call(obj, obj1) => todo!(),
            ExprKind::Method {
                callee,
                generics,
                args,
            } => todo!(),
            ExprKind::Tuple(elems) => todo!(),
            ExprKind::Binary(ast_bin_op_kind, lhs, rhs) => todo!(),
            ExprKind::Unary(ast_un_op_kind, obj) => todo!(),
            ExprKind::Literal(ast_lit) => todo!(),
            ExprKind::FuncLit(obj, spanned) => todo!(),
            ExprKind::TraitMethodLit {
                method,
                trait_params,
                method_params,
            } => todo!(),
            ExprKind::TypeMethodLit { ty, name, params } => todo!(),
            ExprKind::Cast(obj, spanned) => todo!(),
            ExprKind::If {
                cond,
                truthy,
                falsy,
            } => todo!(),
            ExprKind::While(obj, obj1) => todo!(),
            ExprKind::ForLoop { pat, iter, body } => todo!(),
            ExprKind::Loop(obj) => todo!(),
            ExprKind::Block(obj) => todo!(),
            ExprKind::Assign(obj, obj1) => todo!(),
            ExprKind::AssignOp(ast_bin_op_kind, obj, obj1) => todo!(),
            ExprKind::Field(obj, ident) => todo!(),
            ExprKind::Index(obj, obj1) => todo!(),
            ExprKind::Range(obj, obj1, ast_range_limits) => todo!(),
            ExprKind::Local(local) => self.local_types[local],
            ExprKind::AddrOf(mutability, pointee) => self.check_expr(expr),
            ExprKind::Break { label, expr } => todo!(),
            ExprKind::Continue { label } => todo!(),
            ExprKind::Return(obj) => todo!(),
            ExprKind::Struct(obj) => todo!(),
        };

        debug_assert!(
            self.pre_coerce_expr_types
                .insert(expr, pre_coerce_expr_ty)
                .is_none()
        );

        pre_coerce_expr_ty
    }
}
