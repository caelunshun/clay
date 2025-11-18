use crate::{
    base::{Session, analysis::SpannedViewEncode, arena::Obj},
    semantic::{
        analysis::{InferCx, TyCtxt},
        syntax::{
            Block, Expr, ExprKind, FuncLocal, SimpleTyKind, SpannedTy, SpannedTyList,
            SpannedTyView, TyKind,
        },
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

    fn check_block(&mut self, block: Obj<Block>) -> SpannedTy {
        let s = self.icx.session();

        todo!()
    }

    fn check_exprs_with_equate(
        &mut self,
        expr: impl IntoIterator<Item = Obj<Expr>>,
        demand: Option<SpannedTy>,
    ) -> SpannedTy {
        todo!()
    }

    fn check_expr(&mut self, expr: Obj<Expr>) -> SpannedTy {
        let s = self.session();
        let tcx = self.tcx();

        let pre_coerce_expr_ty = match &expr.r(s).kind {
            ExprKind::Array(elems) => {
                let elem_ty = self.check_exprs_with_equate(elems.r(s).iter().copied(), None);

                todo!();
            }
            ExprKind::Call(callee, args) => todo!(),
            ExprKind::Method {
                callee,
                generics,
                args,
            } => todo!(),
            ExprKind::Tuple(elems) => {
                let elems = elems
                    .r(s)
                    .iter()
                    .map(|elem| self.check_expr(*elem))
                    .collect::<Vec<_>>();

                SpannedTyView::Tuple(SpannedTyList::alloc_list(expr.r(s).span, &elems, tcx))
                    .encode(expr.r(s).span, tcx)
            }
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
            } => {
                self.check_exprs_with_equate(
                    [*cond],
                    Some(SpannedTy::new_unspanned(
                        tcx.intern_ty(TyKind::Simple(SimpleTyKind::Bool)),
                    )),
                );

                self.check_exprs_with_equate([*truthy, *falsy], None)
            }
            ExprKind::While(cond, block) => {
                self.check_exprs_with_equate(
                    [*cond],
                    Some(SpannedTy::new_unspanned(
                        tcx.intern_ty(TyKind::Simple(SimpleTyKind::Bool)),
                    )),
                );

                self.check_block(*block);

                SpannedTy::new_unspanned(tcx.intern_ty(TyKind::Tuple(tcx.intern_ty_list(&[]))))
            }
            ExprKind::ForLoop { pat, iter, body } => todo!(),
            ExprKind::Loop(block) => todo!(),
            ExprKind::Block(block) => self.check_block(*block),
            ExprKind::Assign(lhs, rhs) => todo!(),
            ExprKind::AssignOp(op, lhs, rhs) => todo!(),
            ExprKind::Field(obj, ident) => todo!(),
            ExprKind::Index(obj, obj1) => todo!(),
            ExprKind::Range(obj, obj1, ast_range_limits) => todo!(),
            ExprKind::Local(local) => self.local_types[local],
            ExprKind::AddrOf(mutability, pointee) => {
                SpannedTy::new_unspanned(tcx.intern_ty(TyKind::Reference(
                    self.icx.fresh_re(),
                    *mutability,
                    self.check_expr(*pointee).value,
                )))
            }
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
