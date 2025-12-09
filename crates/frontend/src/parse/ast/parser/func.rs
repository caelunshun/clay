use crate::{
    base::{
        Diag, ErrorGuaranteed, LeafDiag,
        syntax::{Bp, HasSpan as _, InfixBp, Matcher, Span},
    },
    kw,
    parse::{
        ast::{
            AstAssignOpKind, AstBinOpKind, AstBinOpSpanned, AstBindingMode, AstBlock, AstBoolLit,
            AstExpr, AstExprField, AstExprKind, AstExprPath, AstExprPathKind, AstFnArg, AstFnDef,
            AstGenericParam, AstGenericParamKind, AstLit, AstMatchArm, AstOptMutability, AstPat,
            AstPatField, AstPatFieldKind, AstPatKind, AstPatStructRest, AstQualification, AstRangeExpr,
            AstRangeLimits, AstStmt, AstStmtKind, AstStmtLet, AstStructRest, AstTy, AstTyKind,
            AstUnOpKind,
            basic::{parse_mutability, parse_paramed_path, parse_paramed_path_no_guard},
            bp::expr_bp,
            entry::P,
            types::{parse_generic_param_list, parse_return_ty, parse_ty},
            utils::{
                match_char_lit, match_eos, match_group, match_ident, match_kw, match_lifetime,
                match_num_lit, match_punct, match_punct_any, match_punct_disambiguate,
                match_punct_seq, match_str_lit, parse_comma_group,
                parse_delimited_until_terminator,
            },
        },
        token::{GroupDelimiter, Lifetime},
    },
    punct, puncts, symbol,
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
        const ALLOW_STRUCT_CTOR = 1 << 1;

        const IN_SCRUTINEE = 0;
        const IN_COND = 0;
        const ALLOW_REGULAR = Self::ALLOW_BLOCK.bits() | Self::ALLOW_STRUCT_CTOR.bits();
    }
}

pub fn parse_expr_full(p: P) -> AstExpr {
    let expr = parse_expr_or_error(p, AstExprFlags::ALLOW_REGULAR);

    if !match_eos(p) {
        p.stuck().ignore_not_in_loop();
    }

    expr
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

    // Parse an `_` expression (useful for pattern-like expressions such as `(foo, _) = (1, 2);`).
    if match_kw(kw!("_")).expect(p).is_some() {
        return Some(build_expr(AstExprKind::Underscore, p));
    }

    // Parse an expression path.
    if let Some(path) = parse_expr_path(p) {
        if flags.contains(AstExprFlags::ALLOW_STRUCT_CTOR)
            && let Some(group) = match_group(GroupDelimiter::Brace).expect(p)
        {
            let p2 = &mut p.enter(&group);

            let mut fields = Vec::new();

            loop {
                let Some(name) = match_ident().expect(p2) else {
                    break;
                };

                if match_punct(punct!(',')).expect(p2).is_some() {
                    fields.push(AstExprField { name, expr: None });
                    continue;
                }

                if match_punct(punct!(':')).expect(p2).is_none() {
                    break;
                }

                let expr = parse_expr_or_error(p2, AstExprFlags::ALLOW_REGULAR);

                fields.push(AstExprField {
                    name,
                    expr: Some(Box::new(expr)),
                });

                if match_punct(punct!(',')).expect(p2).is_none() {
                    break;
                }
            }

            let rest = match match_punct_seq(puncts!("..")).expect(p2) {
                Some(sp) => match parse_expr(p, AstExprFlags::ALLOW_REGULAR) {
                    Some(exp) => AstStructRest::Base(Box::new(exp)),
                    None => AstStructRest::Rest(sp),
                },
                None => AstStructRest::None,
            };

            if !match_eos(p2) {
                p2.stuck().ignore_not_in_loop();
            }

            return Some(build_expr(AstExprKind::Struct(path, fields, rest), p));
        }

        return Some(build_expr(AstExprKind::Path(path), p));
    }

    // Parse a literal
    if let Some(lit) = parse_expr_literal_as_expr(p) {
        return Some(lit);
    }

    // Parse an array.
    if let Some(group) = match_group(GroupDelimiter::Bracket).expect(p) {
        let res = parse_comma_group(&mut p.enter(&group), |p| {
            parse_expr_or_error(p, AstExprFlags::ALLOW_REGULAR)
        });

        return Some(build_expr(AstExprKind::Array(res.elems), p));
    }

    // Parse a parenthesis or tuple.
    if let Some(paren) = match_group(GroupDelimiter::Paren).expect(p) {
        let res = parse_comma_group(&mut p.enter(&paren), |p| {
            parse_expr_or_error(p, AstExprFlags::ALLOW_REGULAR)
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
        let label = parse_label(p);

        if let Some(block) = parse_expr_pratt_block_seed(p, seed_start, label) {
            return Some(block);
        }

        if label.is_some() {
            return Some(build_expr(AstExprKind::Error(p.stuck().error()), p));
        }
    }

    // Parse a `match` expression
    if match_kw(kw!("match")).expect(p).is_some() {
        let Some(scrutinee) = parse_expr(p, AstExprFlags::IN_SCRUTINEE) else {
            return Some(build_expr(AstExprKind::Error(p.stuck().error()), p));
        };

        let Some(braced) = match_group(GroupDelimiter::Brace).expect(p) else {
            return Some(build_expr(AstExprKind::Error(p.stuck().error()), p));
        };

        let arms = parse_delimited_until_terminator(
            &mut p.enter(&braced),
            &mut (),
            |p, _| parse_match_arm(p),
            |p, _| match_punct(punct!(',')).expect(p).is_some(),
            |p, _| match_eos(p),
        )
        .elems;

        return Some(build_expr(AstExprKind::Match(Box::new(scrutinee), arms), p));
    }

    // Match `let` expressions in `if` conditions.
    if match_kw(kw!("let")).expect(p).is_some() {
        let pat = parse_pat(p);

        let Some(eq) = match_punct(punct!('=')).expect(p) else {
            return Some(build_expr(AstExprKind::Error(p.stuck().error()), p));
        };

        let Some(rhs) = parse_expr_pratt(p, AstExprFlags::IN_SCRUTINEE, expr_bp::PRE_LET.right)
        else {
            return Some(build_expr(AstExprKind::Error(p.stuck().error()), p));
        };

        return Some(build_expr(
            AstExprKind::Let(Box::new(pat), Box::new(rhs), eq.span),
            p,
        ));
    }

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

    // Match prefix range expressions
    if let Some((span, limits)) = parse_expr_range_limits(p) {
        let rhs = parse_expr_pratt(p, flags, expr_bp::PRE_RANGE.right);

        return Some(AstExpr {
            span,
            kind: AstExprKind::Range(AstRangeExpr {
                low: None,
                high: rhs.map(Box::new),
                limits,
            }),
        });
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
            let cond = parse_expr_or_error(p, AstExprFlags::IN_COND);

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
        let Some(cond) = parse_expr(p, AstExprFlags::IN_COND) else {
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

    // Parse a `for` expression
    if match_kw(kw!("for")).expect(p).is_some() {
        let pat = parse_pat(p);

        if match_kw(kw!("in")).expect(p).is_none() {
            return build_expr(AstExprKind::Error(p.stuck().error()), p);
        }

        let Some(iter) = parse_expr(p, AstExprFlags::IN_SCRUTINEE) else {
            return build_expr(AstExprKind::Error(p.stuck().error()), p);
        };

        let Some(block) = parse_brace_block(p) else {
            return build_expr(AstExprKind::Error(p.stuck().error()), p);
        };

        return build_expr(
            AstExprKind::ForLoop {
                pat: Box::new(pat),
                iter: Box::new(iter),
                body: Box::new(block),
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

pub fn parse_expr_literal_as_expr(p: P) -> Option<AstExpr> {
    parse_expr_literal(p).map(|lit| AstExpr {
        span: lit.span(),
        kind: AstExprKind::Lit(lit),
    })
}

pub fn parse_expr_literal(p: P) -> Option<AstLit> {
    let mut p = p.to_parse_guard(symbol!("literal expression"));
    let p = &mut *p;

    let start = p.next_span();

    // Parse a boolean literal.
    if match_kw(kw!("true")).expect(p).is_some() {
        return Some(AstLit::Bool(AstBoolLit {
            span: start,
            value: true,
        }));
    }

    if match_kw(kw!("false")).expect(p).is_some() {
        return Some(AstLit::Bool(AstBoolLit {
            span: start,
            value: false,
        }));
    }

    // Parse a string literal.
    if let Some(lit) = match_str_lit().expect(p) {
        return Some(AstLit::String(lit));
    }

    // Parse a character literal.
    if let Some(lit) = match_char_lit().expect(p) {
        return Some(AstLit::Char(lit));
    }

    // Parse a numeric literal.
    if let Some(lit) = match_num_lit().expect(p) {
        return Some(AstLit::Number(lit));
    }

    None
}

pub fn parse_label(p: P) -> Option<Lifetime> {
    let lt = match_lifetime().expect_to_parse(p, symbol!("block label"))?;

    if match_punct(punct!(':')).expect(p).is_none() {
        p.stuck().ignore_not_in_loop();
    }

    Some(lt)
}

pub fn parse_match_arm(p: P) -> AstMatchArm {
    let start = p.next_span();

    let pat = parse_pat(p);

    let guard = match_kw(kw!("if"))
        .expect(p)
        .map(|_| Box::new(parse_expr_or_error(p, AstExprFlags::IN_COND)));

    if match_punct_seq(puncts!("=>")).expect(p).is_none() {
        p.stuck().ignore_not_in_loop();
    }

    let expr = parse_expr_or_error(p, AstExprFlags::ALLOW_REGULAR);

    AstMatchArm {
        span: start.to(p.prev_span()),
        pat: Box::new(pat),
        guard,
        body: Box::new(expr),
    }
}

pub fn parse_expr_pratt_chain(p: P, flags: AstExprFlags, min_bp: Bp, seed: AstExpr) -> AstExpr {
    let mut lhs = seed;

    // Parse postfix and infix operations that bind tighter than our caller.
    'chaining: loop {
        // Match infix range expressions
        if expr_bp::INFIX_RANGE.left >= min_bp
            && let Some((span, limits)) = parse_expr_range_limits(p)
        {
            let rhs = parse_expr_pratt(p, flags, expr_bp::INFIX_RANGE.right);

            lhs = AstExpr {
                span,
                kind: AstExprKind::Range(AstRangeExpr {
                    low: Some(Box::new(lhs)),
                    high: rhs.map(Box::new),
                    limits,
                }),
            };

            continue 'chaining;
        }

        // Match indexing
        if let Some(group) = match_group(GroupDelimiter::Bracket)
            .maybe_expect(p, expr_bp::POST_BRACKET.left >= min_bp)
        {
            let index = parse_expr_full(&mut p.enter(&group));

            lhs = AstExpr {
                span: group.span,
                kind: AstExprKind::Index(Box::new(lhs), Box::new(index)),
            };

            continue 'chaining;
        }

        // Match calls
        if let Some(paren) =
            match_group(GroupDelimiter::Paren).maybe_expect(p, expr_bp::POST_CALL.left >= min_bp)
        {
            let res = parse_comma_group(&mut p.enter(&paren), |p| {
                parse_expr_or_error(p, AstExprFlags::ALLOW_REGULAR)
            });

            lhs = AstExpr {
                span: paren.span,
                kind: AstExprKind::Call(Box::new(lhs), res.elems),
            };

            continue 'chaining;
        }

        // Match named indexes
        if let Some(dot) =
            match_punct(punct!('.')).maybe_expect(p, expr_bp::POST_DOT.left >= min_bp)
        {
            if match_kw(kw!("as")).expect(p).is_some() {
                if match_punct_seq(puncts!("::")).expect(p).is_none() {
                    p.stuck().ignore_about_to_break();

                    break 'chaining;
                }

                let Some(generics) = parse_generic_param_list(p) else {
                    p.stuck().ignore_about_to_break();

                    break 'chaining;
                };

                let ty = if let [
                    AstGenericParam {
                        kind: AstGenericParamKind::PositionalTy(ty),
                        ..
                    },
                ] = generics.list.as_slice()
                {
                    ty.clone()
                } else {
                    AstTy {
                        span: generics.span,
                        kind: AstTyKind::Error(
                            Diag::span_err(generics.span, "expected a single type").emit(),
                        ),
                    }
                };

                lhs = AstExpr {
                    span: dot.span.to(p.prev_span()),
                    kind: AstExprKind::Cast(Box::new(lhs), Box::new(ty)),
                };

                continue 'chaining;
            }

            let Some(name) = match_ident().expect(p) else {
                p.stuck().ignore_about_to_break();

                break 'chaining;
            };

            if match_punct_seq(puncts!("::")).expect(p).is_some() {
                let Some(generics) = parse_generic_param_list(p) else {
                    p.stuck().ignore_not_in_loop();

                    continue 'chaining;
                };

                let Some(args) = match_group(GroupDelimiter::Paren).expect(p) else {
                    p.stuck().ignore_not_in_loop();

                    continue 'chaining;
                };

                let args = parse_comma_group(&mut p.enter(&args), |p| {
                    parse_expr_or_error(p, AstExprFlags::ALLOW_REGULAR)
                })
                .elems;

                lhs = AstExpr {
                    span: dot.span.to(name.span),
                    kind: AstExprKind::GenericMethodCall {
                        target: Box::new(lhs),
                        method: name,
                        generics: Box::new(generics),
                        args,
                    },
                };

                continue 'chaining;
            }

            lhs = AstExpr {
                span: dot.span.to(name.span),
                kind: AstExprKind::Field(Box::new(lhs), name),
            };

            continue 'chaining;
        }

        let mut p = p.to_parse_guard(symbol!("operator"));
        let p = &mut *p;

        // Match punctuation-demarcated infix operations
        type PunctSeqInfixOp = (AstBinOpKind, InfixBp);

        const PUNCT_SEQ_INFIX_COMPUTE_OPS: [PunctSeqInfixOp; 8] = [
            (AstBinOpKind::And, expr_bp::INFIX_LOGICAL_AND),
            (AstBinOpKind::Or, expr_bp::INFIX_LOGICAL_OR),
            (AstBinOpKind::Eq, expr_bp::INFIX_EQ),
            (AstBinOpKind::Ne, expr_bp::INFIX_NEQ),
            (AstBinOpKind::Le, expr_bp::INFIX_LTE),
            (AstBinOpKind::Ge, expr_bp::INFIX_GTE),
            (AstBinOpKind::Shl, expr_bp::INFIX_BIT_SHL),
            (AstBinOpKind::Shr, expr_bp::INFIX_BIT_SHR),
        ];

        for (kind, op_bp) in PUNCT_SEQ_INFIX_COMPUTE_OPS {
            if let Some(span) = match_punct_any(kind.punct()).maybe_expect(p, op_bp.left >= min_bp)
            {
                let rhs = parse_expr_pratt_or_error(p, flags, op_bp.right);

                lhs = AstExpr {
                    span: lhs.span.to(p.prev_span()),
                    kind: AstExprKind::Binary(
                        AstBinOpSpanned { span, kind },
                        Box::new(lhs),
                        Box::new(rhs),
                    ),
                };

                continue 'chaining;
            }
        }

        type PunctSeqInfixAssignOp = (AstAssignOpKind, InfixBp);

        const PUNCT_SEQ_INFIX_ASSIGN_OPS: [PunctSeqInfixAssignOp; 10] = [
            (AstAssignOpKind::Add, expr_bp::INFIX_ASSIGN_ADD),
            (AstAssignOpKind::Sub, expr_bp::INFIX_ASSIGN_SUB),
            (AstAssignOpKind::Mul, expr_bp::INFIX_ASSIGN_MUL),
            (AstAssignOpKind::Div, expr_bp::INFIX_ASSIGN_DIV),
            (AstAssignOpKind::Rem, expr_bp::INFIX_ASSIGN_REM),
            (AstAssignOpKind::BitXor, expr_bp::INFIX_ASSIGN_BIT_XOR),
            (AstAssignOpKind::BitAnd, expr_bp::INFIX_ASSIGN_BIT_AND),
            (AstAssignOpKind::BitOr, expr_bp::INFIX_ASSIGN_BIT_OR),
            (AstAssignOpKind::Shl, expr_bp::INFIX_ASSIGN_SHL),
            (AstAssignOpKind::Shr, expr_bp::INFIX_ASSIGN_SHR),
        ];

        for (kind, op_bp) in PUNCT_SEQ_INFIX_ASSIGN_OPS {
            if let Some(span) = match_punct_any(kind.punct()).maybe_expect(p, op_bp.left >= min_bp)
            {
                let rhs = parse_expr_pratt_or_error(p, flags, op_bp.right);

                lhs = AstExpr {
                    span,
                    kind: AstExprKind::AssignOp(kind, Box::new(lhs), Box::new(rhs)),
                };

                continue 'chaining;
            }
        }

        type PunctInfixOp = (AstBinOpKind, InfixBp);

        const PUNCT_INFIX_OPS: [PunctInfixOp; 10] = [
            (AstBinOpKind::Add, expr_bp::INFIX_ADD),
            (AstBinOpKind::Sub, expr_bp::INFIX_SUB),
            (AstBinOpKind::Mul, expr_bp::INFIX_MUL),
            (AstBinOpKind::Div, expr_bp::INFIX_DIV),
            (AstBinOpKind::Rem, expr_bp::INFIX_REM),
            (AstBinOpKind::BitXor, expr_bp::INFIX_BIT_XOR),
            (AstBinOpKind::BitAnd, expr_bp::INFIX_BIT_AND),
            (AstBinOpKind::BitOr, expr_bp::INFIX_BIT_OR),
            (AstBinOpKind::Lt, expr_bp::INFIX_LT),
            (AstBinOpKind::Gt, expr_bp::INFIX_GT),
        ];

        for (kind, op_bp) in PUNCT_INFIX_OPS {
            if let Some(span) = match_punct_any(kind.punct()).maybe_expect(p, op_bp.left >= min_bp)
            {
                let rhs = parse_expr_pratt_or_error(p, flags, op_bp.right);

                lhs = AstExpr {
                    span: lhs.span.to(p.prev_span()),
                    kind: AstExprKind::Binary(
                        AstBinOpSpanned { span, kind },
                        Box::new(lhs),
                        Box::new(rhs),
                    ),
                };

                continue 'chaining;
            }
        }

        // Match infix assignment
        if let Some(punct) = match_punct_disambiguate(punct!('='), &[puncts!("=>")])
            .maybe_expect(p, expr_bp::INFIX_ASSIGN.left >= min_bp)
        {
            lhs = AstExpr {
                span: punct.span,
                kind: AstExprKind::Assign(
                    Box::new(lhs),
                    Box::new(parse_expr_pratt_or_error(
                        p,
                        flags,
                        expr_bp::INFIX_ASSIGN.right,
                    )),
                ),
            };
        }

        break;
    }

    lhs
}

pub fn parse_expr_range_limits(p: P) -> Option<(Span, AstRangeLimits)> {
    let start = p.next_span();

    if match_punct_seq(puncts!("..=")).expect(p).is_some() {
        return Some((start.to(p.prev_span()), AstRangeLimits::Closed));
    }

    if match_punct_seq(puncts!("..")).expect(p).is_some() {
        return Some((start.to(p.prev_span()), AstRangeLimits::HalfOpen));
    }

    None
}

pub fn parse_expr_path(p: P) -> Option<AstExprPath> {
    let mut p = p.to_parse_guard(symbol!("path"));
    let p = &mut p;

    let start = p.next_span();

    if let Some(self_kw) = match_kw(kw!("Self")).expect(p) {
        let rest = if match_punct_seq(puncts!("::")).expect(p).is_some() {
            match parse_paramed_path_no_guard(p) {
                Some(path) => Some(path),
                None => {
                    return Some(AstExprPath {
                        span: start.to(p.prev_span()),
                        kind: AstExprPathKind::Error(p.stuck().error()),
                    });
                }
            }
        } else {
            None
        };

        return Some(AstExprPath {
            span: start.to(p.prev_span()),
            kind: AstExprPathKind::SelfTy(self_kw.span, rest),
        });
    }

    match parse_qualification(p) {
        Some(qualification) => {
            let Some(rest) = match_punct_seq(puncts!("::"))
                .expect(p)
                .and_then(|_| parse_paramed_path_no_guard(p))
            else {
                return Some(AstExprPath {
                    span: start.to(p.prev_span()),
                    kind: AstExprPathKind::Error(p.stuck().error()),
                });
            };

            Some(AstExprPath {
                span: start.to(p.prev_span()),
                kind: AstExprPathKind::Qualified(Box::new(qualification), rest),
            })
        }
        None => {
            let rest = parse_paramed_path(p)?;

            Some(AstExprPath {
                span: start.to(p.prev_span()),
                kind: AstExprPathKind::Bare(rest),
            })
        }
    }
}

pub fn parse_qualification(p: P) -> Option<AstQualification> {
    let start = p.next_span();

    match_punct(punct!('<')).expect(p)?;

    let self_ty = parse_ty(p);
    let as_trait = match_kw(kw!("as")).expect(p).map(|_| parse_ty(p));

    if match_punct(punct!('>')).expect(p).is_none() {
        p.stuck().ignore_not_in_loop();
    }

    Some(AstQualification {
        span: start.to(p.prev_span()),
        self_ty,
        as_trait,
    })
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

                let ascription = match_punct(punct!(':'))
                    .expect(p)
                    .map(|_| Box::new(parse_ty(p)));

                if match_punct(punct!('=')).expect(p).is_none() {
                    if match_punct(punct!(';')).expect(p).is_none() {
                        p.stuck().ignore_not_in_loop();
                    }

                    stmts.push(AstStmt {
                        span: let_kw.span.to(p.prev_span()),
                        kind: AstStmtKind::Let(AstStmtLet {
                            pat: Box::new(binding),
                            ascription,
                            init: None,
                            else_clause: None,
                        }),
                    });

                    continue;
                }

                let init = parse_expr_or_error(p, AstExprFlags::ALLOW_REGULAR);

                let else_clause = match_kw(kw!("else")).expect(p).and_then(|_| {
                    let block = parse_brace_block(p).map(Box::new);

                    if block.is_none() {
                        p.stuck().ignore_not_in_loop();
                    }

                    block
                });

                if match_punct(punct!(';')).expect(p).is_none() {
                    p.stuck().ignore_not_in_loop();
                }

                stmts.push(AstStmt {
                    span: let_kw.span.to(p.prev_span()),
                    kind: AstStmtKind::Let(AstStmtLet {
                        pat: Box::new(binding),
                        ascription,
                        init: Some(Box::new(init)),
                        else_clause,
                    }),
                });

                continue 'stmt;
            }

            // Parse as an expression.
            parse_expr(p, AstExprFlags::ALLOW_REGULAR)
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
    _ = match_punct(punct!('|')).expect(p);

    parse_pat_no_top_alt(p)
}

pub fn parse_pat_no_top_alt(p: P) -> AstPat {
    let start = p.next_span();

    let mut alts = Vec::new();

    loop {
        alts.push(parse_pat_single_arm(p));

        if match_punct(punct!('|')).expect(p).is_none() {
            break;
        }
    }

    if alts.len() == 1 {
        alts.into_iter().next().unwrap()
    } else {
        AstPat {
            span: start.to(p.prev_span()),
            kind: AstPatKind::Or(alts),
        }
    }
}

pub fn parse_pat_single_arm(p: P) -> AstPat {
    let seed_start = p.next_span();
    let build_pat = move |kind: AstPatKind, p: P| AstPat {
        span: seed_start.to(p.prev_span()),
        kind,
    };

    // Parse holes
    if match_kw(kw!("_")).expect(p).is_some() {
        return build_pat(AstPatKind::Hole, p);
    }

    // Parse rest
    if match_punct_seq(puncts!("..")).expect(p).is_some() {
        return build_pat(AstPatKind::Rest, p);
    }

    // Parse tuples
    if let Some(group) = match_group(GroupDelimiter::Paren).expect(p) {
        return match parse_comma_group(&mut p.enter(&group), parse_pat).into_singleton() {
            Ok(singleton) => build_pat(AstPatKind::Paren(Box::new(singleton)), p),
            Err(elems) => build_pat(AstPatKind::Tuple(elems), p),
        };
    }

    // Parse slices
    if let Some(group) = match_group(GroupDelimiter::Bracket).expect(p) {
        return build_pat(
            AstPatKind::Slice(parse_comma_group(&mut p.enter(&group), parse_pat).elems),
            p,
        );
    }

    // Parse references
    if match_punct(punct!('&')).expect(p).is_some() {
        let muta = parse_mutability(p);

        return build_pat(AstPatKind::Ref(muta, Box::new(parse_pat_single_arm(p))), p);
    }

    // Parse literal variants
    if let Some(lit) = parse_expr_literal_as_expr(p) {
        if let Some((_sp, limits)) = parse_expr_range_limits(p) {
            return build_pat(
                AstPatKind::Range(AstRangeExpr {
                    low: Some(Box::new(lit)),
                    high: parse_pat_lit_expr(p).map(Box::new),
                    limits,
                }),
                p,
            );
        }

        return build_pat(AstPatKind::Lit(Box::new(lit)), p);
    }

    // Parse identifier variants
    let binding_mode = parse_binding_mode(p);

    if let Some(path) = parse_expr_path(p) {
        let and_bind = match_punct(punct!('@'))
            .expect(p)
            .map(|_| Box::new(parse_pat_single_arm(p)));

        if and_bind.is_none() {
            let hint_muta_prefix = || {
                LeafDiag::span_note(
                    binding_mode.span(),
                    "mutability prefix not allowed in front of match structures",
                )
            };

            // Parse tuple struct pattern
            if let Some(group) = match_group(GroupDelimiter::Paren).expect_or_hint(
                p,
                !binding_mode.was_specified(),
                |_, _| hint_muta_prefix(),
            ) {
                return build_pat(
                    AstPatKind::PathAndParen(
                        path,
                        parse_comma_group(&mut p.enter(&group), parse_pat).elems,
                    ),
                    p,
                );
            }

            // Parse braced struct pattern
            if let Some(group) = match_group(GroupDelimiter::Brace).expect_or_hint(
                p,
                !binding_mode.was_specified(),
                |_, _| hint_muta_prefix(),
            ) {
                let p2 = &mut p.enter(&group);

                let mut fields = Vec::new();

                loop {
                    let start = p2.next_span();

                    let muta = parse_mutability(p2);

                    let Some(name) = match_ident().expect(p2) else {
                        break;
                    };

                    if match_punct(punct!(',')).expect(p2).is_some() {
                        fields.push(AstPatField {
                            span: start.to(p2.prev_span()),
                            name,
                            kind: AstPatFieldKind::Bare(muta),
                        });
                        continue;
                    }

                    if muta.was_explicit() || match_punct(punct!(':')).expect(p2).is_none() {
                        fields.push(AstPatField {
                            span: start.to(p2.prev_span()),
                            name,
                            kind: AstPatFieldKind::Bare(muta),
                        });
                        break;
                    }

                    let expr = parse_pat(p2);

                    fields.push(AstPatField {
                        span: start.to(p2.prev_span()),
                        name,
                        kind: AstPatFieldKind::WithPat(Box::new(expr)),
                    });

                    if match_punct(punct!(',')).expect(p2).is_none() {
                        break;
                    }
                }

                let rest = match match_punct_seq(puncts!("..")).expect(p2) {
                    Some(sp) => AstPatStructRest::Rest(sp),
                    None => AstPatStructRest::None,
                };

                if !match_eos(p2) {
                    p2.stuck().ignore_not_in_loop();
                }

                return build_pat(AstPatKind::PathAndBrace(path, fields, rest), p);
            }

            // Parse range pattern
            if let Some((_sp, limits)) = parse_expr_range_limits(p) {
                return build_pat(
                    AstPatKind::Range(AstRangeExpr {
                        low: Some(Box::new(AstExpr {
                            span: path.span,
                            kind: AstExprKind::Path(path),
                        })),
                        high: parse_pat_lit_expr(p).map(Box::new),
                        limits,
                    }),
                    p,
                );
            }
        }

        return build_pat(
            AstPatKind::Path {
                binding_mode,
                path,
                and_bind,
            },
            p,
        );
    }

    if binding_mode.was_specified() {
        return build_pat(AstPatKind::Error(p.stuck().error()), p);
    }

    build_pat(AstPatKind::Error(p.stuck().error()), p)
}

pub fn parse_binding_mode(p: P) -> AstBindingMode {
    match parse_mutability(p) {
        AstOptMutability::Mut(a) => {
            match parse_mutability(p) {
                // `mut mut`
                AstOptMutability::Mut(b) => AstBindingMode {
                    by_ref: AstOptMutability::Mut(a),
                    local_muta: AstOptMutability::Mut(b),
                },
                // `mut ref`
                AstOptMutability::Ref(b) => AstBindingMode {
                    by_ref: AstOptMutability::Mut(a),
                    local_muta: AstOptMutability::Ref(b),
                },
                // `mut`
                AstOptMutability::Implicit => AstBindingMode {
                    by_ref: AstOptMutability::Implicit,
                    local_muta: AstOptMutability::Mut(a),
                },
            }
        }
        AstOptMutability::Ref(a) => {
            match parse_mutability(p) {
                // `ref mut`
                AstOptMutability::Mut(b) => AstBindingMode {
                    by_ref: AstOptMutability::Ref(a),
                    local_muta: AstOptMutability::Mut(b),
                },
                // `ref ref`
                AstOptMutability::Ref(b) => AstBindingMode {
                    by_ref: AstOptMutability::Ref(a),
                    local_muta: AstOptMutability::Ref(b),
                },
                // `ref`
                AstOptMutability::Implicit => AstBindingMode {
                    by_ref: AstOptMutability::Implicit,
                    local_muta: AstOptMutability::Ref(a),
                },
            }
        }
        AstOptMutability::Implicit => AstBindingMode {
            by_ref: AstOptMutability::Implicit,
            local_muta: AstOptMutability::Implicit,
        },
    }
}

pub fn parse_pat_lit_expr(p: P) -> Option<AstExpr> {
    if let Some(lit) = parse_expr_literal_as_expr(p) {
        return Some(lit);
    }

    if let Some(path) = parse_expr_path(p) {
        return Some(AstExpr {
            span: path.span,
            kind: AstExprKind::Path(path),
        });
    }

    None
}
