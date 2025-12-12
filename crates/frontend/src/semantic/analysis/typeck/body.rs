use crate::{
    base::{Session, arena::Obj},
    semantic::{
        analysis::{CrateTypeckVisitor, TyCtxt, TyVisitor},
        syntax::{
            Block, Divergence, Expr, ExprKind, FnDef, FuncLocal, GenericBinder, Pat, Re,
            SpannedTyOrReList, Ty, TyAndDivergence, TyKind,
        },
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

// === Body Walking === //

pub trait TyCheckPhase<'tcx> {
    // === Context === //

    fn tcx(&self) -> &'tcx TyCtxt;

    fn session(&self) -> &'tcx Session {
        &self.tcx().session
    }

    // === Inference === //

    /// Obtains a fresh region for inference.
    fn fresh_re(&mut self) -> Re;

    /// Normalizes inference variables to their known types.
    fn reveal_ty(&mut self, ty: Ty) -> Ty;

    /// Obtains a local's type inference variable.
    fn local_ty(&mut self, local: Obj<FuncLocal>) -> Ty;

    /// Type-checks a collection of expressions, ensuring they all have the same type and that they
    /// can be coerced to meet a given demand. Returns the type of the expression after coercion.
    fn check_expr(
        &mut self,
        exprs: impl IntoIterator<Item = Obj<Expr>>,
        demand: Option<Ty>,
    ) -> TyAndDivergence;

    /// Type-checks a block and ensures it can be coerced into the demand type. Returns the type of
    /// the block after the coercion.
    fn check_block(&mut self, block: Obj<Block>, demand: Option<Ty>) -> TyAndDivergence;

    /// Check that a type is well-formed as soon as possible.
    fn queue_wf(&mut self, ty: Ty);

    /// Check that a generic parameter list is well-formed as soon as possible.
    fn queue_wf_binder(&mut self, args: SpannedTyOrReList, binder: Obj<GenericBinder>);

    // === Visitation === //

    /// Walks a block, making demands of other blocks and expressions.
    fn visit_block(&mut self, block: Obj<Block>) -> TyAndDivergence {
        todo!();
    }

    /// Walks an expression, making demands of other blocks and expressions.
    fn visit_expr(&mut self, expr: Obj<Expr>) -> TyAndDivergence {
        let s = self.session();
        let tcx = self.tcx();

        let mut divergence = Divergence::MayDiverge;

        let ty = match &*expr.r(s).kind {
            ExprKind::Array(elems) => {
                let elem_ty = self.check_expr(elems.r(s).iter().copied(), None);

                todo!();
            }
            ExprKind::Call(callee, args) => todo!(),
            ExprKind::Method {
                callee,
                generics,
                args,
            } => todo!(),
            ExprKind::Tuple(elems) => tcx.intern_ty(TyKind::Tuple(
                tcx.intern_ty_list(
                    &elems
                        .r(s)
                        .iter()
                        .map(|elem| divergence.and_do(self.check_expr([*elem], None)))
                        .collect::<Vec<_>>(),
                ),
            )),
            ExprKind::Let(pat, scrutinee) => todo!(),
            ExprKind::Binary(op, lhs, rhs) => todo!(),
            ExprKind::Unary(ast_un_op_kind, obj) => todo!(),
            ExprKind::Literal(ast_lit) => todo!(),
            ExprKind::TupleOrUnitCtor(instance) => todo!(),
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
            ExprKind::While(cond, block) => todo!(),
            ExprKind::ForLoop { pat, iter, body } => todo!(),
            ExprKind::Match(scrutinee, arms) => todo!(),
            ExprKind::Loop(block) => todo!(),
            ExprKind::Block(block) => divergence.and_do(self.check_block(*block, None)),
            ExprKind::Assign(lhs, rhs) => todo!(),
            ExprKind::AssignOp(op, lhs, rhs) => todo!(),
            ExprKind::Field(obj, ident) => todo!(),
            ExprKind::GenericMethodCall {
                target,
                method,
                generics,
                args,
            } => todo!(),
            ExprKind::Index(obj, obj1) => todo!(),
            ExprKind::Range(range) => todo!(),
            ExprKind::LocalSelf => todo!(),
            ExprKind::Local(local) => self.local_ty(*local),
            ExprKind::AddrOf(mutability, pointee) => tcx.intern_ty(TyKind::Reference(
                self.fresh_re(),
                *mutability,
                divergence.and_do(self.check_expr([*pointee], None)),
            )),
            ExprKind::Break { label, expr } => todo!(),
            ExprKind::Continue { label } => todo!(),
            ExprKind::Return(obj) => todo!(),
            ExprKind::Struct(obj) => todo!(),
            ExprKind::Error(err) => tcx.intern_ty(TyKind::Error(*err)),
        };

        TyAndDivergence { ty, divergence }
    }

    fn demanded_pat_ty(&mut self, pat: Obj<Pat>) -> Ty {
        todo!()
    }
}
