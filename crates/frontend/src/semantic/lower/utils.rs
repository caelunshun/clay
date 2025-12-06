use crate::{
    base::syntax::Span,
    parse::ast::{AstBinOpKind, AstExpr, AstExprKind},
};

pub fn fold_right_associative_ast_bin_ops(
    expr: &AstExpr,
    op_kind: AstBinOpKind,
) -> Vec<(Option<Span>, &AstExpr)> {
    let mut accum = Vec::new();
    let mut finger = expr;

    loop {
        if let AstExprKind::Binary(op, op_span, lhs, rhs) = &finger.kind
            && op_kind == *op
        {
            accum.push((Some(*op_span), &**rhs));
            finger = lhs;
        } else {
            accum.push((None, finger));
            break;
        }
    }

    accum.reverse();

    accum
}
