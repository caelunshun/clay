use super::{
    AstAdt, AstBlock, AstExpr, AstExprKind, AstField, AstFuncDef, AstFuncGeneric, AstFuncParam,
    AstMatchArm, AstMember, AstPat, AstPatKind, AstStmt, AstStmtKind, Keyword, MetaTypeKind,
    Mutability, PunctSeq, kw, puncts, ty_bp,
};
use crate::{
    base::{
        LeafDiag, Level, Session,
        syntax::{Bp, InfixBp, Matcher, OptPResult, OptPResultExt, Span},
    },
    parse::{
        ast::{AdtKind, BinOpKind, LiteralKind, UnaryOpKind, expr_bp},
        token::{
            GroupDelimiter, Ident, Punct, TokenCharLit, TokenCursor, TokenGroup, TokenMatcher,
            TokenNumLit, TokenParser, TokenPunct, TokenStrLit, token_matcher,
        },
    },
    punct, symbol,
};

type P<'a, 'g> = &'a mut TokenParser<'g>;
type C<'a, 'g> = &'a mut TokenCursor<'g>;

// === ADT Parsing === //

pub fn parse_file(tokens: &TokenGroup) -> AstAdt {
    let mut p = TokenParser::new(tokens);

    parse_adt_contents(&mut p, AdtKind::Mod)
}

fn parse_adt_contents(p: P, kind: AdtKind) -> AstAdt {
    let mut fields = Vec::new();
    let mut members = Vec::new();

    let start = p.next_span();

    loop {
        if match_eos(p) {
            break;
        }

        let is_public = match_kw(kw!("pub")).expect(p).is_some();

        // Parse `const <name> = <expr>;` members.
        if let Some(member) = parse_ast_member_const(p, is_public).did_match() {
            if let Ok(member) = member {
                members.push(member);
            }

            // recovery strategy: continue parsing where we left off.

            continue;
        }

        // Parse `<name>: <ty>;` fields.
        if kind.can_have_fields() {
            if let Some(field) = parse_adt_field(p, is_public).did_match() {
                if let Ok(field) = field {
                    fields.push(field);
                }

                // recovery strategy: continue parsing where we left off.

                continue;
            }
        } else {
            p.hint_if_passes(
                |c, _| {
                    if match_ident().consume(c).is_none() {
                        return false;
                    }

                    if match_punct(punct!(':')).consume(c).is_none() {
                        return false;
                    }

                    let start = c.prev_span();
                    let file = start.lo.file();
                    let start = file.pos_to_loc(start.lo).line;

                    c.lookahead(|c| {
                        loop {
                            if c.peek().is_none() {
                                return false;
                            }

                            if file.pos_to_loc(c.next_span().lo).line != start {
                                return false;
                            }

                            if match_punct(punct!(';')).consume(c).is_some() {
                                return true;
                            }

                            c.eat();
                        }
                    });

                    true
                },
                |sp, _| LeafDiag::span_note(sp, "modules cannot define fields"),
            );
        }

        p.stuck_recover().eat();
    }

    AstAdt {
        span: start.to(p.prev_span()),
        kind,
        fields,
        members,
    }
}

fn parse_adt_field(p: P, is_public: bool) -> OptPResult<AstField> {
    // Match name
    let Some(name) = match_ident().expect(p) else {
        return Ok(None);
    };

    // Match annotation colon
    if match_punct(punct!(':')).expect(p).is_none() {
        return Err(p.stuck());
    }

    // Match type
    let ty = parse_ty(p);

    // Match semi-colon.
    if match_punct(punct!(';')).expect(p).is_none() {
        return Err(p.stuck());
    }

    Ok(Some(AstField {
        name,
        ty: Box::new(ty),
        is_public,
    }))
}

fn parse_ast_member_const(p: P, is_public: bool) -> OptPResult<AstMember> {
    // Match `const`
    if match_kw(kw!("const")).expect(p).is_none() {
        return Ok(None);
    }

    // Match const name
    let Some(name) = match_ident().expect(p) else {
        return Err(p.stuck());
    };

    // Match equals symbol
    if match_punct(punct!('=')).expect(p).is_none() {
        return Err(p.stuck());
    }

    // Match initializer.
    let initializer = parse_expr(p, ExprParseFlags::NO_RESTRICTIONS);

    // Match semi-colon.
    if match_punct(punct!(';')).expect(p).is_none() {
        return Err(p.stuck());
    }

    Ok(Some(AstMember {
        name,
        init: Box::new(initializer),
        is_public,
    }))
}

// === Expression parsing === //

bitflags::bitflags! {
    #[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
    struct ExprParseFlags : u32 {
        const NO_RESTRICTIONS = !0;
        const IN_BLOCK = Self::ALLOW_STRUCT_CTOR.bits();
        const IN_SCRUTINEE = Self::ALLOW_CONST_BLOCK.bits();

        const ALLOW_STRUCT_CTOR = 1 << 0;
        const ALLOW_CONST_BLOCK = 1 << 1;
    }
}

fn parse_expr_full(p: P) -> AstExpr {
    let expr = parse_expr(p, ExprParseFlags::NO_RESTRICTIONS);

    if !match_eos(p) {
        // Recovery strategy: ignore
        let _ = p.stuck();
    }

    expr
}

fn parse_expr(p: P, flags: ExprParseFlags) -> AstExpr {
    parse_expr_pratt(p, Bp::MIN, flags)
}

fn parse_expr_pratt(p: P, min_bp: Bp, flags: ExprParseFlags) -> AstExpr {
    parse_expr_pratt_inner(p, min_bp, false, flags).unwrap()
}

fn parse_expr_pratt_opt(p: P, min_bp: Bp, flags: ExprParseFlags) -> Option<AstExpr> {
    parse_expr_pratt_inner(p, min_bp, true, flags)
}

// See: https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
fn parse_expr_pratt_inner(
    p: P,
    min_bp: Bp,
    is_optional: bool,
    flags: ExprParseFlags,
) -> Option<AstExpr> {
    let seed = parse_expr_pratt_inner_seed(p, is_optional, flags)?;

    Some(parse_expr_pratt_inner_chain(p, min_bp, flags, seed))
}

fn parse_expr_pratt_inner_seed(p: P, is_optional: bool, flags: ExprParseFlags) -> Option<AstExpr> {
    // Parse seed expression
    let seed_start = p.next_span();
    let build_expr = move |expr: AstExprKind, p: P| {
        Some(AstExpr {
            span: seed_start.to(p.prev_span()),
            kind: expr,
        })
    };

    // Parse seeds common with type expressions.
    if let Some(expr) = parse_common_expr_seeds(p, flags) {
        return Some(expr);
    }

    // Parse a parenthesis or tuple.
    if let Some(paren) = match_group(GroupDelimiter::Paren).expect(p) {
        let res = parse_comma_group(&mut p.enter(&paren), |p| {
            parse_expr(p, ExprParseFlags::NO_RESTRICTIONS)
        });

        return build_expr(
            match res.into_singleton() {
                Ok(expr) => AstExprKind::Paren(Box::new(expr)),
                Err(exprs) => AstExprKind::Tuple(exprs),
            },
            p,
        );
    }

    // Parse an array.
    if let Some(array) = match_group(GroupDelimiter::Bracket).expect(p) {
        return build_expr(
            AstExprKind::Array(
                parse_comma_group(&mut p.enter(&array), |p| {
                    parse_expr(p, ExprParseFlags::NO_RESTRICTIONS)
                })
                .elems,
            ),
            p,
        );
    }

    // Parse a block expression
    if let Some(block) = parse_brace_block(p) {
        // TODO: Labels
        return build_expr(AstExprKind::Block(Box::new(block)), p);
    }

    // Parse a function expression
    if match_kw(kw!("fn")).expect(p).is_some() {
        let sig_start = p.next_span();

        let generics = match_punct(punct!('<')).expect(p).map(|_| {
            parse_delimited(
                p,
                &mut (),
                |p, _| parse_func_generic(p),
                |p, _| match_punct(punct!(',')).expect(p).is_some(),
                |p, _| match_punct(punct!('>')).expect(p).is_some(),
            )
            .elems
        });

        let params = match_group(GroupDelimiter::Paren)
            .expect(p)
            .map(|group| parse_comma_group(&mut p.enter(&group), parse_func_param).elems);

        if generics.is_none() && params.is_none() {
            p.hint(LeafDiag::new(
                    Level::Note,
                    "both generic and runtime arguments are optional for a function but at least one must be present",
                ));

            // Recovery strategy: ignore
            p.stuck_recover_with(|_| {});
        }

        let ret_ty = match_punct_seq(puncts!("->"))
            .expect(p)
            .map(|_| Box::new(parse_ty(p)));

        let sig_span = sig_start.to(p.prev_span());

        let Some(body) = parse_brace_block(p) else {
            // Recovery strategy: ignore
            return build_expr(AstExprKind::Error(p.stuck_recover_with(|_| {})), p);
        };

        return build_expr(
            AstExprKind::FuncDef(Box::new(AstFuncDef {
                sig_span,
                generics: generics.unwrap_or_default(),
                params,
                ret_ty,
                body: Box::new(body),
            })),
            p,
        );
    }

    // Parse a `use` expression
    if match_kw(kw!("use")).expect(p).is_some() {
        let Some(block) = match_group(GroupDelimiter::Paren).expect(p) else {
            // Recovery strategy: do nothing
            return build_expr(AstExprKind::Error(p.stuck_recover_with(|_| {})), p);
        };

        let mut p2 = p.enter(&block);

        let Some(name) = match_str_lit().expect(&mut p2) else {
            // Recovery strategy: do nothing
            return build_expr(AstExprKind::Error(p.stuck_recover_with(|_| {})), p);
        };

        if !match_eos(&mut p2) {
            p2.stuck_recover_with(|_| {
                // Recovery strategy: ignore
            });
        }

        return build_expr(AstExprKind::Use(Box::new(name)), p);
    }

    // Parse a `type` expression
    if match_kw(kw!("type")).expect(p).is_some() {
        let Some(block) = match_group(GroupDelimiter::Paren).expect(p) else {
            // Recovery strategy: do nothing
            return build_expr(AstExprKind::Error(p.stuck_recover_with(|_| {})), p);
        };

        let ty = parse_ty_full(&mut p.enter(&block));

        return build_expr(AstExprKind::TypeExpr(Box::new(ty)), p);
    }

    // Parse an `if` expression
    if match_kw(kw!("if")).expect(p).is_some() {
        fn parse_after_if(if_span: Span, p: P) -> AstExpr {
            let cond = parse_expr(p, ExprParseFlags::IN_SCRUTINEE);

            let Some(truthy) = parse_brace_block(p) else {
                // Recovery strategy: do nothing
                return AstExpr {
                    span: if_span.to(p.next_span()),
                    kind: AstExprKind::Error(p.stuck().0),
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
                    label: None,
                    span: falsy.span,
                    stmts: vec![],
                    last_expr: Some(falsy),
                }
            } else {
                // Match bare `else`
                let Some(falsy) = parse_brace_block(p) else {
                    // Recovery strategy: do nothing
                    return AstExpr {
                        span: if_span.to(p.next_span()),
                        kind: AstExprKind::Error(p.stuck().0),
                    };
                };

                falsy
            };

            AstExpr {
                span: self_span,
                kind: AstExprKind::If {
                    cond: Box::new(cond),
                    truthy: Box::new(truthy),
                    falsy: Some(Box::new(falsy)),
                },
            }
        }

        return Some(parse_after_if(seed_start, p));
    }

    // Parse a `while` expression
    if match_kw(kw!("while")).expect(p).is_some() {
        // TODO: Labels

        let cond = parse_expr(p, ExprParseFlags::IN_SCRUTINEE);

        let Some(block) = parse_brace_block(p) else {
            // Recovery strategy: do nothing
            return build_expr(AstExprKind::Error(p.stuck().0), p);
        };

        return build_expr(
            AstExprKind::While {
                cond: Box::new(cond),
                block: Box::new(block),
            },
            p,
        );
    }

    // Parse a `loop` expression
    if match_kw(kw!("loop")).expect(p).is_some() {
        // TODO: Labels

        let Some(block) = parse_brace_block(p) else {
            // Recovery strategy: do nothing
            return build_expr(AstExprKind::Error(p.stuck().0), p);
        };

        return build_expr(AstExprKind::Loop(Box::new(block)), p);
    }

    // Parse a `match` expression
    if match_kw(kw!("match")).expect(p).is_some() {
        let scrutinee = parse_expr(p, ExprParseFlags::IN_SCRUTINEE);

        let Some(braced) = match_group(GroupDelimiter::Brace).expect(p) else {
            // Recovery strategy: do nothing
            return build_expr(AstExprKind::Error(p.stuck().0), p);
        };

        let arms = parse_delimited(
            &mut p.enter(&braced),
            &mut (),
            |p, _| parse_match_arm(p),
            |p, _| match_punct(punct!(',')).expect(p).is_some(),
            |p, _| match_eos(p),
        )
        .elems;

        return build_expr(
            AstExprKind::Match {
                scrutinee: Box::new(scrutinee),
                arms,
            },
            p,
        );
    }

    // Parse a `return` expression
    if match_kw(kw!("return")).expect(p).is_some() {
        let expr = parse_expr_pratt_opt(p, expr_bp::PRE_RETURN.right, flags);

        return build_expr(AstExprKind::Return(expr.map(Box::new)), p);
    }

    // Parse a `continue` expression
    if match_kw(kw!("continue")).expect(p).is_some() {
        return build_expr(AstExprKind::Continue, p);
    }

    // Parse a `break` expression
    if match_kw(kw!("break")).expect(p).is_some() {
        // TODO: Labels

        let expr = parse_expr_pratt_opt(p, expr_bp::PRE_BREAK.right, flags);

        return build_expr(AstExprKind::Break(expr.map(Box::new)), p);
    }

    // Parse unary neg.
    if match_punct(punct!('-')).expect(p).is_some() {
        let lhs = parse_expr_pratt(p, expr_bp::PRE_NEG.right, flags);

        return build_expr(AstExprKind::Unary(UnaryOpKind::Neg, Box::new(lhs)), p);
    }

    // Parse unary not.
    if match_punct(punct!('!')).expect(p).is_some() {
        let lhs = parse_expr_pratt(p, expr_bp::PRE_NOT.right, flags);

        return build_expr(AstExprKind::Unary(UnaryOpKind::Not, Box::new(lhs)), p);
    }

    if is_optional {
        None
    } else {
        // Recovery strategy: eat a token
        build_expr(
            AstExprKind::Error(p.stuck_recover_with(|c| {
                c.eat();
            })),
            p,
        )
    }
}

fn parse_expr_pratt_inner_chain(p: P, min_bp: Bp, flags: ExprParseFlags, seed: AstExpr) -> AstExpr {
    let mut lhs = seed;

    // Parse postfix and infix operations that bind tighter than our caller.
    'chaining: loop {
        // Match chaining syntaxes common with types.
        {
            let (new_lhs, did_chain) = parse_common_expr_chains(p, lhs, min_bp);
            lhs = new_lhs;

            if did_chain {
                continue 'chaining;
            }
        }

        // Match infix assignment
        if let Some(punct) =
            match_punct(punct!('=')).maybe_expect(p, expr_bp::INFIX_ASSIGN.left >= min_bp)
        {
            lhs = AstExpr {
                span: punct.span,
                kind: AstExprKind::Assign(
                    Box::new(lhs),
                    Box::new(parse_expr_pratt(p, expr_bp::INFIX_ASSIGN.right, flags)),
                ),
            };
        }

        // Match punctuation-demarcated infix operations
        type PunctSeqInfixOp = (PunctSeq, InfixBp, BinOpKind);

        const PUNCT_SEQ_INFIX_OPS: [PunctSeqInfixOp; 4] = [
            (puncts!("^^"), expr_bp::INFIX_POW, BinOpKind::Pow),
            (
                puncts!("&&"),
                expr_bp::INFIX_LOGICAL_AND,
                BinOpKind::LogicalAnd,
            ),
            (
                puncts!("||"),
                expr_bp::INFIX_LOGICAL_OR,
                BinOpKind::LogicalOr,
            ),
            (puncts!("=="), expr_bp::INFIX_EQ, BinOpKind::Eq),
        ];

        for (punct_seq, op_bp, kind) in PUNCT_SEQ_INFIX_OPS {
            if let Some(span) = match_punct_seq(punct_seq).maybe_expect(p, op_bp.left >= min_bp) {
                lhs = AstExpr {
                    span,
                    kind: AstExprKind::Bin(
                        kind,
                        Box::new(lhs),
                        Box::new(parse_expr_pratt(p, op_bp.right, flags)),
                    ),
                };

                continue 'chaining;
            }
        }

        type PunctInfixOp = (Punct, InfixBp, BinOpKind);

        const PUNCT_INFIX_OPS: [PunctInfixOp; 8] = [
            (punct!('+'), expr_bp::INFIX_ADD, BinOpKind::Add),
            (punct!('-'), expr_bp::INFIX_SUB, BinOpKind::Sub),
            (punct!('*'), expr_bp::INFIX_MUL, BinOpKind::Mul),
            (punct!('/'), expr_bp::INFIX_DIV, BinOpKind::Div),
            (punct!('%'), expr_bp::INFIX_MOD, BinOpKind::Mod),
            (punct!('&'), expr_bp::INFIX_BIT_AND, BinOpKind::BitAnd),
            (punct!('|'), expr_bp::INFIX_BIT_OR, BinOpKind::BitOr),
            (punct!('^'), expr_bp::INFIX_BIT_XOR, BinOpKind::BitXor),
        ];

        for (punct, op_bp, kind) in PUNCT_INFIX_OPS {
            if let Some(op_punct) = match_punct(punct).maybe_expect(p, op_bp.left >= min_bp) {
                lhs = AstExpr {
                    span: op_punct.span,
                    kind: AstExprKind::Bin(
                        kind,
                        Box::new(lhs),
                        Box::new(parse_expr_pratt(p, op_bp.right, flags)),
                    ),
                };

                continue 'chaining;
            }
        }

        // Parse a constructor expression
        if flags.contains(ExprParseFlags::ALLOW_STRUCT_CTOR)
            && !matches!(lhs.kind, AstExprKind::New(..))
            && let Some(braced) = match_group(GroupDelimiter::Brace).expect(p)
        {
            let initializers = parse_comma_group(&mut p.enter(&braced), |p| {
                let name = match_ident().expect(p)?;

                if match_punct(punct!(':')).expect(p).is_none() {
                    return Some((name, None));
                }

                Some((
                    name,
                    Some(Box::new(parse_expr(p, ExprParseFlags::NO_RESTRICTIONS))),
                ))
            })
            .elems
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();

            lhs = AstExpr {
                span: braced.span,
                kind: AstExprKind::New(Box::new(lhs), initializers),
            };
            continue 'chaining;
        }

        break;
    }

    lhs
}

fn parse_expr_const_block(p: P, const_kw: Ident) -> Option<AstExpr> {
    let group = match_group(GroupDelimiter::Brace).expect(p)?;

    let seed = AstExpr {
        span: Span::new(const_kw.span.lo, group.span.hi),
        kind: AstExprKind::ConstBlock(Box::new(parse_block(&mut p.enter(&group), None))),
    };

    Some(parse_expr_pratt_inner_chain(
        p,
        Bp::MIN,
        ExprParseFlags::NO_RESTRICTIONS,
        seed,
    ))
}

fn parse_match_arm(p: P) -> AstMatchArm {
    let pat = parse_pat(p);

    if match_punct_seq(puncts!("=>")).expect(p).is_none() {
        // Recovery strategy: ignore
        p.stuck_recover_with(|_| {});
    }

    let expr = parse_expr(p, ExprParseFlags::NO_RESTRICTIONS);

    AstMatchArm { pat, expr }
}

fn parse_ty_full(p: P) -> AstExpr {
    let expr = parse_ty(p);

    if !match_eos(p) {
        // Recovery strategy: ignore
        let _ = p.stuck();
    }

    expr
}

fn parse_ty(p: P) -> AstExpr {
    parse_ty_pratt(p, Bp::MIN)
}

fn parse_ty_pratt(p: P, min_bp: Bp) -> AstExpr {
    let seed = parse_ty_pratt_seed(p);

    parse_ty_pratt_chain(p, min_bp, seed)
}

fn parse_ty_pratt_seed(p: P) -> AstExpr {
    let seed_start = p.next_span();
    let build_expr = move |ty: AstExprKind, p: P| AstExpr {
        span: seed_start.to(p.prev_span()),
        kind: ty,
    };

    // Parse seeds common with value expressions.
    if let Some(expr) = parse_common_expr_seeds(p, ExprParseFlags::NO_RESTRICTIONS) {
        return expr;
    }

    // Parse a parenthesis or tuple type constructor.
    if let Some(paren) = match_group(GroupDelimiter::Paren).expect(p) {
        let res = parse_comma_group(&mut p.enter(&paren), parse_ty);

        return build_expr(
            match res.into_singleton() {
                Ok(expr) => AstExprKind::Paren(Box::new(expr)),
                Err(exprs) => AstExprKind::TypeTuple(exprs),
            },
            p,
        );
    }

    // Parse a block expression.
    if let Some(block) = parse_brace_block(p) {
        return build_expr(AstExprKind::Block(Box::new(block)), p);
    }

    // Parse an array type constructor.
    if let Some(arr) = match_group(GroupDelimiter::Bracket).expect(p) {
        let mut p2 = p.enter(&arr);

        let ty = parse_ty(&mut p2);

        if match_punct(punct!(';')).expect(&mut p2).is_none() {
            // Recovery strategy: ignore and continue
            p2.stuck_recover_with(|_c| {});
        }

        let count = parse_expr_full(&mut p2);

        return build_expr(AstExprKind::TypeArray(Box::new(ty), Box::new(count)), p);
    }

    // Parse a pointer type constructor.
    if match_punct(punct!('*')).expect(p).is_some() {
        let Some(muta) = parse_ptr_mutability(p) else {
            return build_expr(
                AstExprKind::Error(p.stuck_recover_with(|c| {
                    // Recovery strategy: eat the bad identifier; otherwise ignore.
                    match_any_ident(c);
                })),
                p,
            );
        };

        let ty = parse_ty_pratt(p, ty_bp::PRE_POINTER.right);

        return build_expr(AstExprKind::TypePointer(muta, Box::new(ty)), p);
    }

    // Parse various single-keyword types.
    if match_kw(kw!("type")).expect(p).is_some() {
        return build_expr(AstExprKind::TypeMeta(MetaTypeKind::Type), p);
    }

    if match_kw(kw!("Self")).expect(p).is_some() {
        return build_expr(AstExprKind::TypeSelf, p);
    }

    // Parse a function type constructor.
    if match_kw(kw!("fn")).expect(p).is_some() {
        if let Some(group) = match_group(GroupDelimiter::Paren).expect(p) {
            let args = parse_comma_group(&mut p.enter(&group), parse_ty).elems;

            let return_ty = match_punct_seq(puncts!("->"))
                .expect(p)
                .map(|_| parse_ty_pratt(p, ty_bp::PRE_FUNC_RETVAL.right))
                .map(Box::new);

            return build_expr(AstExprKind::TypeFn(args, return_ty), p);
        }

        if match_punct_seq(puncts!("...")).expect(p).is_some() {
            return build_expr(AstExprKind::TypeMeta(MetaTypeKind::Fn), p);
        }

        // Recovery strategy: ignore
        return build_expr(AstExprKind::Error(p.stuck_recover_with(|_| {})), p);
    }

    // Recovery strategy: eat a token
    build_expr(
        AstExprKind::Error(p.stuck_recover_with(|c| {
            c.eat();
        })),
        p,
    )
}

fn parse_ty_pratt_chain(p: P, min_bp: Bp, seed: AstExpr) -> AstExpr {
    let mut lhs = seed;

    'chaining: loop {
        // Match chaining syntaxes common with types.
        {
            let (new_lhs, did_chain) = parse_common_expr_chains(p, lhs, min_bp);
            lhs = new_lhs;

            if did_chain {
                continue 'chaining;
            }
        }

        break;
    }

    lhs
}

fn parse_common_expr_seeds(p: P, flags: ExprParseFlags) -> Option<AstExpr> {
    let seed_start = p.next_span();
    let build_expr = move |expr: AstExprKind, p: P| {
        Some(AstExpr {
            span: seed_start.to(p.prev_span()),
            kind: expr,
        })
    };

    // Parse a name.
    if let Some(ident) = match_ident().expect(p) {
        return build_expr(AstExprKind::Name(ident), p);
    }

    // Parse an intrinsic.
    if match_kw(kw!("intrinsic")).expect(p).is_some() {
        let Some(block) = match_group(GroupDelimiter::Paren).expect(p) else {
            // Recovery strategy: do nothing
            return build_expr(AstExprKind::Error(p.stuck_recover_with(|_| {})), p);
        };

        let mut p2 = p.enter(&block);

        let Some(intrinsic) = match_str_lit().expect(&mut p2) else {
            // Recovery strategy: do nothing
            return build_expr(AstExprKind::Error(p2.stuck_recover_with(|_| {})), p);
        };

        _ = match_eos(&mut p2);

        return build_expr(AstExprKind::Intrinsic(intrinsic.value), p);
    }

    // Parse a boolean literal.
    if match_kw(kw!("true")).expect(p).is_some() {
        return build_expr(AstExprKind::Lit(LiteralKind::BoolLit(true)), p);
    }

    if match_kw(kw!("false")).expect(p).is_some() {
        return build_expr(AstExprKind::Lit(LiteralKind::BoolLit(false)), p);
    }

    // Parse a string literal.
    if let Some(lit) = match_str_lit().expect(p) {
        return build_expr(AstExprKind::Lit(LiteralKind::StrLit(lit)), p);
    }

    // Parse a character literal.
    if let Some(lit) = match_char_lit().expect(p) {
        return build_expr(AstExprKind::Lit(LiteralKind::CharLit(lit)), p);
    }

    // Parse a numeric literal.
    if let Some(lit) = match_num_lit().expect(p) {
        return build_expr(AstExprKind::Lit(LiteralKind::NumLit(lit)), p);
    }

    // Parse ADTs.
    if let Some(kind) = parse_adt_kind(p) {
        let Some(group) = match_group(GroupDelimiter::Brace).expect(p) else {
            return build_expr(
                AstExprKind::Error(p.stuck_recover_with(|_| {
                    // Recovery strategy: ignore
                })),
                p,
            );
        };

        let contents = parse_adt_contents(&mut p.enter(&group), kind);

        return build_expr(AstExprKind::AdtDef(Box::new(contents)), p);
    }

    // Parse `const` blocks.
    if flags.contains(ExprParseFlags::ALLOW_CONST_BLOCK)
        && let Some(const_kw) = match_kw(kw!("const")).expect(p)
    {
        let Some(expr) = parse_expr_const_block(p, const_kw) else {
            return build_expr(
                AstExprKind::Error(p.stuck_recover_with(|_| {
                    // Recovery strategy: ignore
                })),
                p,
            );
        };

        return Some(expr);
    }

    None
}

#[must_use]
fn parse_common_expr_chains(p: P, mut lhs: AstExpr, min_bp: Bp) -> (AstExpr, bool) {
    // Match indexing
    if let Some(group) =
        match_group(GroupDelimiter::Bracket).maybe_expect(p, expr_bp::POST_BRACKET.left >= min_bp)
    {
        let index = parse_expr_full(&mut p.enter(&group));

        lhs = AstExpr {
            span: group.span,
            kind: AstExprKind::Index(Box::new(lhs), Box::new(index)),
        };

        return (lhs, true);
    }

    // Match calls
    if let Some(paren) =
        match_group(GroupDelimiter::Paren).maybe_expect(p, expr_bp::POST_CALL.left >= min_bp)
    {
        let res = parse_comma_group(&mut p.enter(&paren), |p| {
            parse_expr(p, ExprParseFlags::NO_RESTRICTIONS)
        });

        lhs = AstExpr {
            span: paren.span,
            kind: AstExprKind::Call(Box::new(lhs), res.elems),
        };

        return (lhs, true);
    }

    // Match instantiations and named indexes
    if let Some(dot) = match_punct(punct!('.')).maybe_expect(p, expr_bp::POST_DOT.left >= min_bp) {
        let mut is_dynamic = false;

        if match_punct_seq(puncts!("<<"))
            .expect(p)
            .inspect(|_| {
                is_dynamic = true;
            })
            .is_some()
            || match_punct(punct!('<')).expect(p).is_some()
        {
            let res = parse_delimited(
                p,
                &mut (),
                |p, _| parse_ty(p),
                |p, _| match_punct(punct!(',')).expect(p).is_some(),
                |p, _| {
                    if is_dynamic {
                        match_punct_seq(puncts!(">>")).expect(p).is_some()
                    } else {
                        match_punct(punct!('>')).expect(p).is_some()
                    }
                },
            );

            lhs = AstExpr {
                span: dot.span.to(p.prev_span()),
                kind: AstExprKind::Instantiate {
                    target: Box::new(lhs),
                    generics: res.elems,
                    is_dynamic,
                },
            };
        } else {
            let Some(name) = match_ident().expect(p) else {
                // Recovery strategy: keep trying to chain.
                let _ = p.stuck();
                return (lhs, true);
            };

            lhs = AstExpr {
                span: dot.span.to(name.span),
                kind: AstExprKind::NamedIndex(Box::new(lhs), name),
            };
        }

        return (lhs, true);
    }

    (lhs, false)
}

fn parse_ptr_mutability(p: P) -> Option<Mutability> {
    if match_kw(kw!("const")).expect(p).is_some() {
        return Some(Mutability::Not);
    }

    if match_kw(kw!("mut")).expect(p).is_some() {
        return Some(Mutability::Mut);
    }

    None
}

fn parse_func_param(p: P) -> AstFuncParam {
    let start = p.next_span();

    let binding = parse_pat(p);

    if match_punct(punct!(':')).expect(p).is_none() {
        // Recovery strategy: ignore
        p.stuck_recover_with(|_| {});
    }

    let ty = parse_ty(p);

    AstFuncParam {
        span: start.to(p.prev_span()),
        binding,
        ty,
    }
}

fn parse_func_generic(p: P) -> AstFuncGeneric {
    let start = p.next_span();

    let name = match_ident().expect(p).ok_or_else(|| {
        // Recovery strategy: ignore
        p.stuck().0
    });

    if match_punct(punct!(':')).expect(p).is_none() {
        // Recovery strategy: ignore
        p.stuck_recover_with(|_| {});
    }

    let ty = parse_ty(p);

    AstFuncGeneric {
        span: start.to(p.prev_span()),
        name,
        ty,
    }
}

// === Block parsing === //

fn parse_brace_block(p: P) -> Option<AstBlock> {
    match_group(GroupDelimiter::Brace)
        .expect(p)
        .map(|group| parse_block(&mut p.enter(&group), None))
}

fn parse_block(p: P, label: Option<Ident>) -> AstBlock {
    let start = p.next_span();

    let mut stmts = Vec::new();

    let last_expr = 'stmt: loop {
        // Match EOS without unterminated expression.
        if match_eos(p) {
            break 'stmt None;
        }

        // Match an expression or a statement.
        let expr = 'expr: {
            // Match empty statements.
            if match_punct(punct!(';')).expect(p).is_some() {
                continue 'stmt;
            }

            // Match `let` statements
            if let Some(let_kw) = match_kw(kw!("let")).expect(p) {
                let binding = parse_pat(p);

                if match_punct(punct!('=')).expect(p).is_none() {
                    // Recovery strategy: ignore
                    let _ = p.stuck_recover();
                }

                let init = parse_expr(p, ExprParseFlags::NO_RESTRICTIONS);

                if match_punct(punct!(';')).expect(p).is_none() {
                    // Recovery strategy: ignore
                    let _ = p.stuck_recover();
                }

                stmts.push(AstStmt {
                    span: let_kw.span.to(p.prev_span()),
                    kind: AstStmtKind::Let {
                        binding,
                        init: Box::new(init),
                    },
                });

                continue 'stmt;
            }

            // Match `const` statements and expressions.
            if let Some(const_kw) = match_kw(kw!("const")).expect(p) {
                // Attempt to parse it as an expression.
                if let Some(group) = match_group(GroupDelimiter::Brace).expect(p) {
                    let seed = AstExpr {
                        span: Span::new(const_kw.span.lo, group.span.hi),
                        kind: AstExprKind::ConstBlock(Box::new(parse_block(
                            &mut p.enter(&group),
                            None,
                        ))),
                    };

                    break 'expr parse_expr_pratt_inner_chain(
                        p,
                        Bp::MIN,
                        ExprParseFlags::NO_RESTRICTIONS,
                        seed,
                    );
                }

                let Some(name) = match_ident().expect(p) else {
                    // Recovery strategy: ignore
                    let _ = p.stuck_recover();
                    continue 'stmt;
                };

                if match_punct(punct!('=')).expect(p).is_none() {
                    // Recovery strategy: ignore
                    let _ = p.stuck_recover();
                }

                let init = parse_expr(p, ExprParseFlags::NO_RESTRICTIONS);

                if match_punct(punct!(';')).expect(p).is_none() {
                    // Recovery strategy: ignore
                    let _ = p.stuck_recover();
                }

                stmts.push(AstStmt {
                    span: const_kw.span.to(p.prev_span()),
                    kind: AstStmtKind::Const {
                        name,
                        init: Box::new(init),
                    },
                });

                continue 'stmt;
            }

            // Parse as an expression.
            parse_expr(p, ExprParseFlags::NO_RESTRICTIONS)
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

        if needs_semi && match_punct(punct!(';')).expect(p).is_none() {
            // Recovery strategy: ignore
            let _ = p.stuck_recover();
        }
    };

    AstBlock {
        label,
        span: start.to(p.prev_span()),
        stmts,
        last_expr,
    }
}

// === Patterns === //

fn parse_pat(p: P) -> AstPat {
    let start = p.next_span();
    let kind = parse_pat_inner(p);

    AstPat {
        span: start.to(p.prev_span()),
        kind,
    }
}

fn parse_pat_inner(p: P) -> AstPatKind {
    // Match `mut <name>`.
    if match_kw(kw!("mut")).expect(p).is_some() {
        if let Some(name) = match_ident().expect(p) {
            return AstPatKind::Name(Mutability::Mut, name);
        }

        // Recovery strategy: do nothing
        return AstPatKind::Error(p.stuck_recover_with(|_| {}));
    }

    // Match `<name>`.
    if let Some(name) = match_ident().expect(p) {
        return AstPatKind::Name(Mutability::Not, name);
    }

    // Match holes.
    if match_kw(kw!("_")).expect(p).is_some() {
        return AstPatKind::Hole;
    }

    // Match parens or tuple destructuring
    if let Some(paren) = match_group(GroupDelimiter::Paren).expect(p) {
        return match parse_comma_group(&mut p.enter(&paren), parse_pat).into_singleton() {
            Ok(single) => AstPatKind::Paren(Box::new(single)),
            Err(list) => AstPatKind::Tuple(list),
        };
    }

    // Recovery strategy: do nothing
    AstPatKind::Error(p.stuck_recover_with(|_| {}))
}

// === Parsing helpers === //

fn parse_adt_kind(p: P) -> Option<AdtKind> {
    if match_kw(kw!("mod")).expect(p).is_some() {
        return Some(AdtKind::Mod);
    }

    if match_kw(kw!("struct")).expect(p).is_some() {
        return Some(AdtKind::Struct);
    }

    if match_kw(kw!("enum")).expect(p).is_some() {
        return Some(AdtKind::Enum);
    }

    if match_kw(kw!("union")).expect(p).is_some() {
        return Some(AdtKind::Union);
    }

    None
}

fn match_any_ident(c: C) -> Option<Ident> {
    c.lookahead(|c| Some(*c.eat()?.ident()?))
}

fn match_kw(kw: Keyword) -> impl TokenMatcher<Output = Option<Ident>> {
    token_matcher(kw.expectation_name(), move |c, _h| {
        match_any_ident(c).filter(|v| !v.raw && v.text == kw.symbol())
    })
}

fn match_ident() -> impl TokenMatcher<Output = Option<Ident>> {
    token_matcher(symbol!("identifier"), move |c, h| {
        let ident = match_any_ident(c)?;

        if ident.raw {
            return Some(ident);
        }

        if Keyword::try_new(ident.text.as_str(&Session::fetch())).is_some() {
            h.hint(LeafDiag::new(
                Level::Note,
                format_args!("`{}` is a reserved keyword", ident.text),
            ));

            return None;
        }

        Some(ident)
    })
}

fn match_group(group: GroupDelimiter) -> impl TokenMatcher<Output = Option<TokenGroup>> {
    token_matcher(group.opening_name(), move |c, _| {
        Some(c.eat()?.group().filter(|v| v.delimiter == group)?.clone())
    })
}

fn match_eos(p: P) -> bool {
    let closing_name = p.cursor_unsafe().iter.group().delimiter.closing_name();

    p.expect(closing_name, |v| v.eat().is_none())
}

fn match_punct(punct: Punct) -> impl TokenMatcher<Output = Option<TokenPunct>> {
    token_matcher(punct.expectation_name(), move |c, _| {
        c.eat()
            .and_then(|v| v.punct())
            .filter(|v| v.ch == punct)
            .copied()
    })
}

fn match_punct_seq(punct: PunctSeq) -> impl TokenMatcher<Output = Option<Span>> {
    token_matcher(punct.expectation_name(), move |c, _| {
        let start = c.next_span();

        if punct
            .seq()
            .iter()
            .all(|&v| match_punct(v).consume(c).is_some())
        {
            Some(start.to(c.prev_span()))
        } else {
            None
        }
    })
}

fn match_str_lit() -> impl TokenMatcher<Output = Option<TokenStrLit>> {
    token_matcher(symbol!("string literal"), |c, _| {
        c.eat().and_then(|v| v.str_lit()).copied()
    })
}

fn match_char_lit() -> impl TokenMatcher<Output = Option<TokenCharLit>> {
    token_matcher(symbol!("character literal"), |c, _| {
        c.eat().and_then(|v| v.char_lit()).copied()
    })
}

fn match_num_lit() -> impl TokenMatcher<Output = Option<TokenNumLit>> {
    token_matcher(symbol!("numeric literal"), |c, _| {
        c.eat().and_then(|v| v.num_lit()).copied()
    })
}

struct Delimited<E> {
    elems: Vec<E>,
    trailing: bool,
}

impl<E> Delimited<E> {
    fn is_multi(&self) -> bool {
        self.elems.len() != 1 || self.trailing
    }

    fn into_singleton(mut self) -> Result<E, Vec<E>> {
        if !self.is_multi() {
            Ok(self.elems.pop().unwrap())
        } else {
            Err(self.elems)
        }
    }
}

fn parse_delimited<C: ?Sized, E>(
    p: P,
    cx: &mut C,
    mut match_elem: impl FnMut(P, &mut C) -> E,
    mut match_delimiter: impl FnMut(P, &mut C) -> bool,
    mut match_eos: impl FnMut(P, &mut C) -> bool,
) -> Delimited<E> {
    let mut elems = Vec::new();

    let trailing = loop {
        if match_eos(p, cx) {
            break !elems.is_empty();
        }

        elems.push(match_elem(p, cx));

        if match_eos(p, cx) {
            break false;
        }

        if !match_delimiter(p, cx) {
            if !match_eos(p, cx) {
                // Recovery strategy: ignore.
                p.stuck_recover_with(|_| {});
            }

            break false;
        }
    };

    Delimited { elems, trailing }
}

fn parse_comma_group<E>(p: P, mut match_elem: impl FnMut(P) -> E) -> Delimited<E> {
    parse_delimited(
        p,
        &mut (),
        |p, _| match_elem(p),
        |p, _| match_punct(punct!(',')).expect(p).is_some(),
        |p, _| match_eos(p),
    )
}
