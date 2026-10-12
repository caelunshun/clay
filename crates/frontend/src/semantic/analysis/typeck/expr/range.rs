use crate::{
    base::arena::{HasInterner as _, HasListInterner as _, Obj},
    parse::ast::AstRangeLimits,
    semantic::{
        analysis::typeck::BodyCtxt,
        syntax::{
            AdtInstance, AdtItem, Divergence, DivergenceAnd, DivergenceJoin, HirRangeExpr,
            LangItems, Ty, TyKind, TyOrRe,
        },
    },
};

#[derive(Debug, Copy, Clone)]
pub enum CheckedRangeExpr {
    Full,
    RangeFrom(Ty),
    RangeTo(Ty),
    Range(Ty),
    RangeToInclusive(Ty),
    RangeInclusive(Ty),
}

impl CheckedRangeExpr {
    pub fn elem_ty(self) -> Option<Ty> {
        match self {
            CheckedRangeExpr::RangeFrom(ty)
            | CheckedRangeExpr::RangeTo(ty)
            | CheckedRangeExpr::Range(ty)
            | CheckedRangeExpr::RangeToInclusive(ty)
            | CheckedRangeExpr::RangeInclusive(ty) => Some(ty),
            CheckedRangeExpr::Full => None,
        }
    }

    pub fn lang_item(self, lang_items: &LangItems) -> Obj<AdtItem> {
        match self {
            CheckedRangeExpr::Full => lang_items.range_full().unwrap(),
            CheckedRangeExpr::RangeFrom(_) => lang_items.range_from().unwrap(),
            CheckedRangeExpr::RangeTo(_) => lang_items.range_to().unwrap(),
            CheckedRangeExpr::Range(_) => lang_items.range().unwrap(),
            CheckedRangeExpr::RangeToInclusive(_) => lang_items.range_to_inclusive().unwrap(),
            CheckedRangeExpr::RangeInclusive(_) => lang_items.range_inclusive().unwrap(),
        }
    }

    pub fn range_ty(self, bcx: &mut BodyCtxt<'_, '_>) -> Ty {
        let s = bcx.session();
        let tcx = bcx.tcx();

        tcx.intern(TyKind::Adt(AdtInstance {
            def: self.lang_item(&bcx.krate().r(s).lang_items),
            params: match self.elem_ty() {
                Some(ty) => tcx.intern_list(&[TyOrRe::Ty(ty)]),
                None => tcx.intern_list(&[]),
            },
        }))
    }
}

impl<'tcx> BodyCtxt<'_, 'tcx> {
    pub fn check_range_expr(&mut self, expr: HirRangeExpr) -> DivergenceAnd<CheckedRangeExpr> {
        let mut divergence = Divergence::MayDiverge;

        let HirRangeExpr { low, high, limits } = expr;

        let ty = match (low, high) {
            (None, None) => None,
            (None, Some(rhs)) => Some(self.check_expr(rhs, None).and_do(&mut divergence)),
            (Some(lhs), None) => Some(self.check_expr(lhs, None).and_do(&mut divergence)),
            (Some(lhs), Some(rhs)) => Some(
                self.check_exprs_equate([lhs, rhs], DivergenceJoin::Sequential)
                    .and_do(&mut divergence),
            ),
        };

        let expr = match (low, high, limits) {
            (None, None, AstRangeLimits::HalfOpen) => CheckedRangeExpr::Full,
            (Some(_), None, AstRangeLimits::HalfOpen) => CheckedRangeExpr::RangeFrom(ty.unwrap()),
            (None, Some(_), AstRangeLimits::HalfOpen) => CheckedRangeExpr::RangeTo(ty.unwrap()),
            (Some(_), Some(_), AstRangeLimits::HalfOpen) => CheckedRangeExpr::Range(ty.unwrap()),
            (None, Some(_), AstRangeLimits::Closed) => {
                CheckedRangeExpr::RangeToInclusive(ty.unwrap())
            }
            (Some(_), Some(_), AstRangeLimits::Closed) => {
                CheckedRangeExpr::RangeInclusive(ty.unwrap())
            }
            (_, None, AstRangeLimits::Closed) => {
                unreachable!()
            }
        };

        DivergenceAnd::new(expr, divergence)
    }
}
