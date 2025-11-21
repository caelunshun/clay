use crate::{
    base::{
        ErrorGuaranteed,
        syntax::{Bp, Matcher, Span},
    },
    kw,
    parse::{
        ast::{
            AstBlock, AstBoolLit, AstExpr, AstExprKind, AstFnArg, AstFnDef, AstLit, AstPat,
            AstPatKind, AstStmt, AstStmtKind, AstUnOpKind,
            basic::parse_expr_path,
            bp::expr_bp,
            entry::P,
            types::{parse_generic_param_list, parse_return_ty, parse_ty},
            utils::{
                match_char_lit, match_eos, match_group, match_ident, match_kw, match_lifetime,
                match_num_lit, match_punct, match_str_lit, parse_comma_group,
                parse_delimited_until_terminator,
            },
        },
        token::{GroupDelimiter, Lifetime},
    },
    punct, symbol,
};
use bitflags::bitflags;

// === Functions === //

pub fn parse_func(p: P) -> Result<Option<AstFnDef>, ErrorGuaranteed> {
    let start = p.next_span();

    if match_kw(kw!("fn")).expect(p).is_none() {
        return Ok(None);
    }

    let Some(name) = match_ident().expect(p) else {
        return Err(p.stuck().error());
    };

    let generics = parse_generic_param_list(p);

    let Some(params) = match_group(GroupDelimiter::Paren).expect(p) else {
        return Err(p.stuck().error());
    };

    let args = parse_comma_group(&mut p.enter(&params), parse_func_arg).elems;

    let ret_ty = parse_return_ty(p);

    let body = 'body: {
        if let Some(block) = parse_brace_block(p) {
            break 'body Some(block);
        }

        if match_punct(punct!(';')).expect(p).is_some() {
            break 'body None;
        }

        p.stuck().ignore_not_in_loop();

        None
    };

    Ok(Some(AstFnDef {
        span: start.to(p.prev_span()),
        name,
        generics,
        args,
        ret_ty,
        body,
    }))
}

pub fn parse_func_arg(p: P) -> AstFnArg {
    let start = p.next_span();

    let pat = parse_pat(p);

    if match_punct(punct!(':')).expect(p).is_none() {
        p.stuck().ignore_not_in_loop();
    }

    let ty = parse_ty(p);

    AstFnArg {
        span: start.to(p.prev_span()),
        pat: Box::new(pat),
        ty: Box::new(ty),
    }
}

// === Expressions === //

bitflags! {
    #[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
    pub struct AstExprFlags: u32 {
        const ALLOW_BLOCK = 1 << 0;

        const IN_SCRUTINEE = 0;
        const ALLOW_ALL = !0;
    }
}

pub fn parse_expr(p: P, flags: AstExprFlags) -> Option<AstExpr> {
    parse_expr_pratt(p, flags, Bp::MIN)
}

pub fn parse_expr_or_error(p: P, flags: AstExprFlags) -> AstExpr {
    parse_expr_pratt_or_error(p, flags, Bp::MIN)
}

pub fn parse_expr_pratt(p: P, flags: AstExprFlags, min_bp: Bp) -> Option<AstExpr> {
    let seed = parse_expr_pratt_seed(p, flags)?;

    Some(parse_expr_pratt_chain(p, flags, min_bp, seed))
}

pub fn parse_expr_pratt_or_error(p: P, flags: AstExprFlags, min_bp: Bp) -> AstExpr {
    parse_expr_pratt(p, flags, min_bp).unwrap_or_else(|| AstExpr {
        span: p.next_span(),
        kind: AstExprKind::Error(p.stuck().error()),
    })
}

pub fn parse_expr_pratt_seed(p: P, flags: AstExprFlags) -> Option<AstExpr> {
    let mut p = p.to_parse_guard(symbol!("expression"));
    let p = &mut *p;

    let seed_start = p.next_span();
    let build_expr = move |kind: AstExprKind, p: P| AstExpr {
        span: seed_start.to(p.prev_span()),
        kind,
    };

    // Parse an expression path.
    if let Some(path) = parse_expr_path(p) {
        return Some(build_expr(AstExprKind::Path(path), p));
    }

    // Parse a boolean literal.
    if match_kw(kw!("true")).expect(p).is_some() {
        return Some(build_expr(
            AstExprKind::Lit(AstLit::Bool(AstBoolLit {
                span: seed_start,
                value: true,
            })),
            p,
        ));
    }

    if match_kw(kw!("false")).expect(p).is_some() {
        return Some(build_expr(
            AstExprKind::Lit(AstLit::Bool(AstBoolLit {
                span: seed_start,
                value: false,
            })),
            p,
        ));
    }

    // Parse a string literal.
    if let Some(lit) = match_str_lit().expect(p) {
        return Some(build_expr(AstExprKind::Lit(AstLit::String(lit)), p));
    }

    // Parse a character literal.
    if let Some(lit) = match_char_lit().expect(p) {
        return Some(build_expr(AstExprKind::Lit(AstLit::Char(lit)), p));
    }

    // Parse a numeric literal.
    if let Some(lit) = match_num_lit().expect(p) {
        return Some(build_expr(AstExprKind::Lit(AstLit::Number(lit)), p));
    }

    // Parse an array.
    if let Some(group) = match_group(GroupDelimiter::Bracket).expect(p) {
        let res = parse_comma_group(&mut p.enter(&group), |p| {
            parse_expr_or_error(p, AstExprFlags::ALLOW_ALL)
        });

        return Some(build_expr(AstExprKind::Array(res.elems), p));
    }

    // Parse a parenthesis or tuple.
    if let Some(paren) = match_group(GroupDelimiter::Paren).expect(p) {
        let res = parse_comma_group(&mut p.enter(&paren), |p| {
            parse_expr_or_error(p, AstExprFlags::ALLOW_ALL)
        });

        return Some(build_expr(
            match res.into_singleton() {
                Ok(expr) => AstExprKind::Paren(Box::new(expr)),
                Err(exprs) => AstExprKind::Tuple(exprs),
            },
            p,
        ));
    }

    // Parse a labelled block-like
    if flags.contains(AstExprFlags::ALLOW_BLOCK) {
        let label = match_lifetime().expect_to_parse(p, symbol!("block label"));

        if let Some(block) = parse_expr_pratt_block_seed(p, seed_start, label) {
            return Some(block);
        }

        if label.is_some() {
            return Some(build_expr(AstExprKind::Error(p.stuck().error()), p));
        }
    }

    // // Parse a `match` expression
    // if match_kw(kw!("match")).expect(p).is_some() {
    //     let Some(scrutinee) = parse_expr(p, AstExprFlags::IN_SCRUTINEE) else {
    //         return Some(build_expr(AstExprKind::Error(p.stuck().error()), p));
    //     };
    //
    //     let Some(braced) = match_group(GroupDelimiter::Brace).expect(p) else {
    //         return Some(build_expr(AstExprKind::Error(p.stuck().error()), p));
    //     };
    //
    //     let arms = parse_delimited_until_terminator(
    //         &mut p.enter(&braced),
    //         &mut (),
    //         |p, _| parse_match_arm(p),
    //         |p, _| match_punct(punct!(',')).expect(p).is_some(),
    //         |p, _| match_eos(p),
    //     )
    //     .elems;
    //
    //     return Some(build_expr(AstExprKind::Match(Box::new(scrutinee), arms), p));
    // }

    // Parse a `return` expression
    if match_kw(kw!("return")).expect(p).is_some() {
        let expr = parse_expr_pratt(p, flags, expr_bp::PRE_RETURN.right);

        return Some(build_expr(AstExprKind::Return(expr.map(Box::new)), p));
    }

    // Parse a `continue` expression
    if match_kw(kw!("continue")).expect(p).is_some() {
        let label = match_lifetime().expect_to_parse(p, symbol!("optional label"));

        return Some(build_expr(AstExprKind::Continue(label), p));
    }

    // Parse a `break` expression
    if match_kw(kw!("break")).expect(p).is_some() {
        let label = match_lifetime().expect_to_parse(p, symbol!("optional label"));

        let expr = parse_expr_pratt(p, flags, expr_bp::PRE_BREAK.right);

        return Some(build_expr(AstExprKind::Break(label, expr.map(Box::new)), p));
    }

    // Parse unary operations
    for (punct, op_kind, bp) in [
        (punct!('-'), AstUnOpKind::Neg, expr_bp::PRE_NEG),
        (punct!('!'), AstUnOpKind::Not, expr_bp::PRE_NOT),
        (punct!('&'), AstUnOpKind::Neg, expr_bp::PRE_REF),
    ] {
        if match_punct(punct).expect(p).is_some() {
            let lhs = parse_expr_pratt_or_error(p, flags, bp.right);

            return Some(build_expr(AstExprKind::Unary(op_kind, Box::new(lhs)), p));
        }
    }

    None
}

pub fn parse_expr_pratt_block_seed(
    p: P,
    seed_start: Span,
    label: Option<Lifetime>,
) -> Option<AstExpr> {
    let build_expr = move |kind: AstExprKind, p: P| {
        Some(AstExpr {
            span: seed_start.to(p.prev_span()),
            kind,
        })
    };

    // Parse a block expression
    if let Some(block) = parse_brace_block(p) {
        return build_expr(AstExprKind::Block(Box::new(block), label), p);
    }

    // Parse an `if` expression
    if match_kw(kw!("if")).expect(p).is_some() {
        fn parse_after_if(if_span: Span, p: P) -> AstExpr {
            let cond = parse_expr_or_error(p, AstExprFlags::IN_SCRUTINEE);

            let Some(truthy) = parse_brace_block(p) else {
                return AstExpr {
                    span: if_span.to(p.next_span()),
                    kind: AstExprKind::Error(p.stuck().error()),
                };
            };

            let self_span = if_span.to(p.prev_span());

            // Match `else`
            let Some(_) = match_kw(kw!("else")).expect(p) else {
                // No `if` branch
                return AstExpr {
                    span: self_span,
                    kind: AstExprKind::If {
                        cond: Box::new(cond),
                        truthy: Box::new(truthy),
                        falsy: None,
                    },
                };
            };

            // Match `if`
            let else_if_start = p.next_span();
            let falsy = if match_kw(kw!("if")).expect(p).is_some() {
                let falsy = parse_after_if(else_if_start, p);

                AstBlock {
                    span: falsy.span,
                    stmts: vec![],
                    last_expr: Some(falsy),
                }
            } else {
                // Match bare `else`
                let Some(falsy) = parse_brace_block(p) else {
                    return AstExpr {
                        span: if_span.to(p.next_span()),
                        kind: AstExprKind::Error(p.stuck().error()),
                    };
                };

                falsy
            };

            AstExpr {
                span: self_span,
                kind: AstExprKind::If {
                    cond: Box::new(cond),
                    truthy: Box::new(truthy),
                    falsy: Some(Box::new(AstExpr {
                        span: falsy.span,
                        kind: AstExprKind::Block(Box::new(falsy), None),
                    })),
                },
            }
        }

        return Some(parse_after_if(seed_start, p));
    }

    // Parse a `while` expression
    if match_kw(kw!("while")).expect(p).is_some() {
        let Some(cond) = parse_expr(p, AstExprFlags::IN_SCRUTINEE) else {
            return build_expr(AstExprKind::Error(p.stuck().error()), p);
        };

        let Some(block) = parse_brace_block(p) else {
            return build_expr(AstExprKind::Error(p.stuck().error()), p);
        };

        return build_expr(
            AstExprKind::While {
                cond: Box::new(cond),
                block: Box::new(block),
                label,
            },
            p,
        );
    }

    // Parse a `loop` expression
    if match_kw(kw!("loop")).expect(p).is_some() {
        let Some(block) = parse_brace_block(p) else {
            return build_expr(AstExprKind::Error(p.stuck().error()), p);
        };

        return build_expr(AstExprKind::Loop(Box::new(block), label), p);
    }

    None
}

pub fn parse_expr_pratt_chain(p: P, flags: AstExprFlags, min_bp: Bp, mut seed: AstExpr) -> AstExpr {
    // TODO

    seed
}

// === Block === //

fn parse_brace_block(p: P) -> Option<AstBlock> {
    match_group(GroupDelimiter::Brace)
        .expect(p)
        .map(|group| parse_block(&mut p.enter(&group)))
}

fn parse_block(p: P) -> AstBlock {
    let start = p.next_span();

    let mut stmts = Vec::new();

    let last_expr = 'stmt: loop {
        // TODO: Recover here

        // Match EOS without unterminated expression.
        if match_eos(p) {
            break 'stmt None;
        }

        // Match an expression or a statement.
        let expr = {
            // Match empty statements.
            if match_punct(punct!(';')).expect(p).is_some() {
                continue 'stmt;
            }

            // Match `let` statements
            if let Some(let_kw) = match_kw(kw!("let")).expect(p) {
                let binding = parse_pat(p);

                if match_punct(punct!('=')).expect(p).is_none() {
                    if match_punct(punct!(';')).expect(p).is_none() {
                        p.stuck().ignore_not_in_loop();
                    }

                    stmts.push(AstStmt {
                        span: let_kw.span.to(p.prev_span()),
                        kind: AstStmtKind::Let(Box::new(binding), None),
                    });

                    continue;
                }

                let init = parse_expr_or_error(p, AstExprFlags::ALLOW_ALL);

                if match_punct(punct!(';')).expect(p).is_none() {
                    p.stuck().ignore_not_in_loop();
                }

                stmts.push(AstStmt {
                    span: let_kw.span.to(p.prev_span()),
                    kind: AstStmtKind::Let(Box::new(binding), Some(Box::new(init))),
                });

                continue 'stmt;
            }

            // Parse as an expression.
            parse_expr(p, AstExprFlags::ALLOW_ALL)
        };

        let Some(expr) = expr else {
            if p.stuck().should_break() {
                break None;
            } else {
                continue;
            }
        };

        // If it's an expression, handle semicolons.
        if match_eos(p) {
            break Some(expr);
        }

        let needs_semi = expr.kind.needs_semi();

        stmts.push(AstStmt {
            span: expr.span,
            kind: AstStmtKind::Expr(expr),
        });

        if needs_semi && match_punct(punct!(';')).expect(p).is_none() && p.stuck().should_break() {
            break None;
        }
    };

    AstBlock {
        span: start.to(p.prev_span()),
        stmts,
        last_expr,
    }
}

// === Patterns === //

pub fn parse_pat(p: P) -> AstPat {
    parse_pat_pratt(p, Bp::MIN)
}

pub fn parse_pat_pratt(p: P, min_bp: Bp) -> AstPat {
    let seed = parse_pat_pratt_seed(p);

    parse_pat_pratt_chain(p, min_bp, seed)
}

pub fn parse_pat_pratt_seed(p: P) -> AstPat {
    let seed_start = p.next_span();
    let build_pat = move |kind: AstPatKind, p: P| AstPat {
        span: seed_start.to(p.prev_span()),
        kind,
    };

    // TODO

    build_pat(AstPatKind::Error(p.stuck().error()), p)
}

pub fn parse_pat_pratt_chain(p: P, min_bp: Bp, mut seed: AstPat) -> AstPat {
    // TODO

    seed
}
