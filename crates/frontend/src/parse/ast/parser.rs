use crate::{
    base::{
        ErrorGuaranteed, LeafDiag, Level, Session,
        syntax::{Bp, Matcher as _, Span},
    },
    kw,
    parse::{
        ast::{
            AstAttribute, AstGenericParam, AstGenericParamKind, AstGenericParamList,
            AstImplLikeBody, AstImplLikeMember, AstImplLikeMemberKind, AstItem, AstItemImpl,
            AstItemKind, AstItemModule, AstItemModuleContents, AstItemTrait, AstItemUse,
            AstNamedSpec, AstSimplePath, AstTraitClause, AstTraitClauseList, AstTy, AstTyKind,
            AstUsePath, AstUsePathKind, AstVisibility, AstVisibilityKind, Keyword, PunctSeq,
        },
        token::{
            GroupDelimiter, Ident, Lifetime, Punct, TokenCharLit, TokenCursor, TokenGroup,
            TokenMatcher, TokenNumLit, TokenParser, TokenPunct, TokenStrLit, token_matcher,
        },
    },
    punct, puncts, symbol,
};
use std::rc::Rc;

// === Driver === //

type P<'a, 'g> = &'a mut TokenParser<'g>;
type C<'a, 'g> = &'a mut TokenCursor<'g>;

pub fn parse_file(tokens: &TokenGroup) -> AstItemModuleContents {
    let mut p = TokenParser::new(tokens);

    parse_mod_contents(&mut p)
}

// === Items === //

fn parse_mod_contents(p: P) -> AstItemModuleContents {
    let mut inner_attrs = Vec::new();
    let mut items = Vec::new();

    loop {
        let outer_attrs = if items.is_empty() {
            let mut outer_attrs = Vec::new();

            for attr in parse_attributes(p) {
                if attr.is_inner && outer_attrs.is_empty() {
                    inner_attrs.push(attr);
                } else {
                    outer_attrs.push(attr);
                }
            }

            outer_attrs
        } else {
            parse_attributes(p)
        };

        if let Some(item) = parse_item(p, outer_attrs) {
            items.push(item);
            continue;
        }

        if match_eos(p) {
            break;
        }

        p.stuck_recover_with(|c| {
            c.eat();
        });
    }

    AstItemModuleContents { inner_attrs, items }
}

fn parse_visibility(p: P) -> AstVisibility {
    let start = p.next_span();

    if match_kw(kw!("pub")).expect(p).is_some() {
        if let Some(group) = match_group(GroupDelimiter::Paren).expect(p) {
            let mut p2 = p.enter(&group);

            let Some(path) = parse_simple_path(&mut p2) else {
                p2.stuck_recover_with(|_| {});

                return AstVisibility {
                    span: start.to(p.prev_span()),
                    kind: AstVisibilityKind::Pub,
                };
            };

            if !match_eos(&mut p2) {
                p2.stuck_recover_with(|_| {});
            }

            AstVisibility {
                span: start.to(p.prev_span()),
                kind: AstVisibilityKind::PubIn(path),
            }
        } else {
            AstVisibility {
                span: start.to(p.prev_span()),
                kind: AstVisibilityKind::Pub,
            }
        }
    } else if match_kw(kw!("priv")).expect(p).is_some() {
        AstVisibility {
            span: start.to(p.prev_span()),
            kind: AstVisibilityKind::Priv,
        }
    } else {
        AstVisibility {
            span: start.shrink_to_lo(),
            kind: AstVisibilityKind::Implicit,
        }
    }
}

fn parse_item(p: P, outer_attrs: Vec<AstAttribute>) -> Option<AstItem> {
    let start = p.next_span();

    let vis = parse_visibility(p);

    let uncommitted = outer_attrs.is_empty() && matches!(vis.kind, AstVisibilityKind::Implicit);

    let make_item = |kind, p: &mut TokenParser| AstItem {
        span: start.to(p.prev_span()),
        outer_attrs,
        vis,
        kind,
    };

    if match_kw(kw!("mod")).expect(p).is_some() {
        let Some(name) = match_ident().expect(p) else {
            return Some(make_item(
                AstItemKind::Error(p.stuck_recover_with(|_| {
                    // TODO: Recover more intelligently
                })),
                p,
            ));
        };

        if let Some(group) = match_group(GroupDelimiter::Brace).expect(p) {
            return Some(make_item(
                AstItemKind::Mod(AstItemModule {
                    name,
                    contents: Some(parse_mod_contents(&mut p.enter(&group))),
                }),
                p,
            ));
        } else {
            if match_punct(punct!(';')).expect(p).is_none() {
                p.stuck_recover_with(|_| {});
            }

            return Some(make_item(
                AstItemKind::Mod(AstItemModule {
                    name,
                    contents: None,
                }),
                p,
            ));
        }
    }

    if match_kw(kw!("trait")).expect(p).is_some() {
        let Some(name) = match_ident().expect(p) else {
            return Some(make_item(
                AstItemKind::Error(p.stuck_recover_with(|_| {
                    // TODO: Recover more intelligently
                })),
                p,
            ));
        };

        let generics = parse_generic_param_list(p);
        let body = parse_impl_ish_body(p);

        return Some(make_item(
            AstItemKind::Trait(AstItemTrait {
                name,
                generics,
                body,
            }),
            p,
        ));
    }

    if match_kw(kw!("impl")).expect(p).is_some() {
        let generics = parse_generic_param_list(p);

        let first_ty = parse_ty(p);
        let second_ty = match_kw(kw!("for"))
            .expect(p)
            .is_some()
            .then(|| parse_ty(p));

        let body = parse_impl_ish_body(p);

        return Some(make_item(
            AstItemKind::Impl(AstItemImpl {
                generics,
                first_ty,
                second_ty,
                body,
            }),
            p,
        ));
    }

    if match_kw(kw!("use")).expect(p).is_some() {
        let Some(path) = parse_tree_path(p) else {
            return Some(make_item(
                AstItemKind::Error(p.stuck_recover_with(|_| {
                    // TODO: Recover more intelligently
                })),
                p,
            ));
        };

        if match_punct(punct!(';')).expect(p).is_none() {
            p.stuck_recover_with(|_| {
                // TODO: Recover more intelligently
            });
        }

        return Some(make_item(AstItemKind::Use(AstItemUse { path }), p));
    }

    if !uncommitted {
        return Some(make_item(
            AstItemKind::Error(p.stuck_recover_with(|_| {
                // TODO: Recover more intelligently
            })),
            p,
        ));
    }

    None
}

// === Paths and Attributes === //

fn parse_attributes(p: P) -> Vec<AstAttribute> {
    let mut attrs = Vec::new();

    while let Some(attr) = parse_attribute(p) {
        attrs.push(attr);
    }

    attrs
}

fn parse_attribute(p: P) -> Option<AstAttribute> {
    let start = p.next_span();

    match_punct(punct!('#')).expect(p)?;

    let is_inner = match_punct(punct!('!')).expect(p).is_some();

    let Some(bracket) = match_group(GroupDelimiter::Bracket).expect(p) else {
        p.stuck_recover_with(|_| {
            // TODO: Recover more intelligently
        });
        return None;
    };

    let mut p2 = p.enter(&bracket);

    let Some(path) = parse_simple_path(&mut p2) else {
        p2.stuck_recover_with(|_| {
            // TODO: Recover more intelligently
        });
        return None;
    };

    let Some(paren) = match_group(GroupDelimiter::Paren).expect(&mut p2) else {
        p2.stuck_recover_with(|_| {
            // TODO: Recover more intelligently
        });
        return None;
    };

    if !match_eos(&mut p2) {
        p2.stuck_recover_with(|_| {
            // TODO: Recover more intelligently
        });
        return None;
    }

    Some(AstAttribute {
        span: start.to(p.prev_span()),
        is_inner,
        path,
        args: paren.tokens,
    })
}

fn parse_simple_path(p: P) -> Option<AstSimplePath> {
    let start = p.next_span();

    let mut parts = Vec::new();

    loop {
        let Some(part) = parse_path_part(p) else {
            if !parts.is_empty() {
                p.stuck_recover_with(|_| {
                    // TODO: Recover more intelligently
                });
            }

            break;
        };

        parts.push(part);

        if match_punct_seq(puncts!("::")).expect(p).is_none() {
            break;
        }
    }

    if parts.is_empty() {
        return None;
    }

    Some(AstSimplePath {
        span: start.to(p.prev_span()),
        parts: Rc::from(parts),
    })
}

fn parse_path_part(p: P) -> Option<Ident> {
    if let Some(ident) = match_ident().expect(p) {
        return Some(ident);
    }

    for kw in [kw!("super"), kw!("crate"), kw!("self")] {
        if let Some(ident) = match_kw(kw).expect(p) {
            return Some(ident);
        }
    }

    None
}

fn parse_tree_path(p: P) -> Option<AstUsePath> {
    let start = p.next_span();

    let mut parts = Vec::new();

    let had_trailing_turbo = loop {
        let Some(part) = parse_path_part(p) else {
            break true;
        };

        parts.push(part);

        if match_punct_seq(puncts!("::")).expect(p).is_none() {
            break false;
        }
    };

    if (parts.is_empty() || had_trailing_turbo)
        && let Some(punct) = match_punct(punct!('*')).expect(p)
    {
        return Some(AstUsePath {
            span: start.to(p.prev_span()),
            base: Rc::from(parts),
            kind: AstUsePathKind::Wild(punct.span),
        });
    }

    if !parts.is_empty() && !had_trailing_turbo {
        let rename = match_kw(kw!("as"))
            .expect(p)
            .and_then(|_| match_ident().expect(p));

        return Some(AstUsePath {
            span: start.to(p.prev_span()),
            base: Rc::from(parts),
            kind: AstUsePathKind::Direct(rename),
        });
    }

    if (parts.is_empty() || had_trailing_turbo)
        && let Some(group) = match_group(GroupDelimiter::Brace).expect(p)
    {
        let mut p2 = p.enter(&group);

        let children = parse_delimited_until_terminator(
            &mut p2,
            &mut (),
            |p, ()| parse_tree_path(p),
            |p, ()| match_punct(punct!(',')).expect(p).is_some(),
            |p, ()| match_eos(p),
        );

        return Some(AstUsePath {
            span: start.to(p.prev_span()),
            base: Rc::from(parts),
            kind: AstUsePathKind::Tree(children.elems.into_iter().flatten().collect()),
        });
    }

    if parts.is_empty() {
        return None;
    }

    p.stuck_recover_with(|_| {
        // TODO: Recover more intelligently
    });

    Some(AstUsePath {
        span: start.to(p.prev_span()),
        base: Rc::from(parts),
        kind: AstUsePathKind::Direct(None),
    })
}

// === Trait Clauses === //

fn parse_trait_clause_list(p: P) -> AstTraitClauseList {
    let start = p.next_span();

    let mut clauses = Vec::new();

    loop {
        clauses.push(parse_trait_clause(p));

        if match_punct(punct!('+')).expect(p).is_none() {
            break;
        }
    }

    AstTraitClauseList {
        span: start.to(p.prev_span()),
        clauses,
    }
}

fn parse_trait_clause(p: P) -> Result<AstTraitClause, ErrorGuaranteed> {
    let start = p.next_span();

    if let Some(lifetime) = match_lifetime().expect(p) {
        return Ok(AstTraitClause::Outlives(lifetime));
    }

    if let Some(path) = parse_simple_path(p) {
        let params = parse_generic_param_list(p);

        return Ok(AstTraitClause::Trait(AstNamedSpec {
            span: start.to(p.prev_span()),
            path,
            params,
        }));
    }

    Err(p.stuck_recover_with(|_| {
        // TODO: Recover more intelligently
    }))
}

// === Generic Parameters === //

fn parse_generic_param_list(p: P) -> Option<AstGenericParamList> {
    let start = p.next_span();

    match_punct(punct!('<')).expect(p)?;

    let list = parse_delimited_until_terminator(
        p,
        &mut (),
        |p, ()| parse_generic_param(p),
        |p, ()| match_punct(punct!(',')).expect(p).is_some(),
        |p, ()| match_punct(punct!('>')).expect(p).is_some(),
    )
    .elems;

    Some(AstGenericParamList {
        span: start.to(p.prev_span()),
        list,
    })
}

fn parse_generic_param(p: P) -> AstGenericParam {
    let start = p.next_span();

    if let Some(path) = parse_simple_path(p) {
        if let Some(part) = path.as_ident() {
            if match_punct(punct!(':')).expect(p).is_some() {
                let clauses = parse_trait_clause_list(p);

                return AstGenericParam {
                    span: start.to(p.prev_span()),
                    kind: AstGenericParamKind::InheritTy(part, clauses),
                };
            }

            if match_punct(punct!('=')).expect(p).is_some() {
                let ty = parse_ty(p);

                return AstGenericParam {
                    span: start.to(p.prev_span()),
                    kind: AstGenericParamKind::TyEquals(part, ty),
                };
            }
        }

        let params = parse_generic_param_list(p);
        let seed = AstTy {
            span: start.to(p.prev_span()),
            kind: AstTyKind::Name(path, params),
        };

        let ty = parse_ty_pratt_chain(p, Bp::MIN, seed);

        return AstGenericParam {
            span: start.to(p.prev_span()),
            kind: AstGenericParamKind::PositionalTy(ty),
        };
    }

    if let Some(lt) = match_lifetime().expect(p) {
        if match_punct(punct!(':')).expect(p).is_some() {
            let clauses = parse_trait_clause_list(p);

            return AstGenericParam {
                span: lt.span,
                kind: AstGenericParamKind::InheritRe(lt, clauses),
            };
        } else {
            return AstGenericParam {
                span: lt.span,
                kind: AstGenericParamKind::PositionalRe(lt),
            };
        }
    }

    let ty = parse_ty(p);

    AstGenericParam {
        span: ty.span,
        kind: AstGenericParamKind::PositionalTy(ty),
    }
}

// === Types === //

fn parse_ty_full(p: P) -> AstTy {
    let expr = parse_ty(p);

    if !match_eos(p) {
        // Recovery strategy: ignore
        let _ = p.stuck();
    }

    expr
}

fn parse_ty(p: P) -> AstTy {
    parse_ty_pratt(p, Bp::MIN)
}

fn parse_ty_pratt(p: P, min_bp: Bp) -> AstTy {
    let seed = parse_ty_pratt_seed(p);

    parse_ty_pratt_chain(p, min_bp, seed)
}

fn parse_ty_pratt_seed(p: P) -> AstTy {
    let seed_start = p.next_span();
    let build_ty = move |kind: AstTyKind, p: P| AstTy {
        span: seed_start.to(p.prev_span()),
        kind,
    };

    // Parse path
    if let Some(path) = parse_simple_path(p) {
        return build_ty(AstTyKind::Name(path, parse_generic_param_list(p)), p);
    }

    // Parse `dyn` trait
    if match_kw(kw!("dyn")).expect(p).is_some() {
        let Some(path) = parse_simple_path(p) else {
            return build_ty(
                AstTyKind::Error(p.stuck_recover_with(|_| {
                    // TODO: Recover more intelligently
                })),
                p,
            );
        };

        let params = parse_generic_param_list(p);

        return build_ty(
            AstTyKind::Trait(AstNamedSpec {
                span: path.span.to(p.prev_span()),
                path,
                params,
            }),
            p,
        );
    }

    // Parse reference
    if match_punct(punct!('&')).expect(p).is_some() {
        return build_ty(
            AstTyKind::Reference(
                match_lifetime().expect(p),
                Box::new(parse_ty_pratt(p, bps::PRE_TY_REF.right)),
            ),
            p,
        );
    }

    // Parse tuple
    // TODO

    // Parse infer
    if match_kw(kw!("_")).expect(p).is_some() {
        return build_ty(AstTyKind::Infer, p);
    }

    // Recovery strategy: eat a token
    build_ty(
        AstTyKind::Error(p.stuck_recover_with(|c| {
            c.eat();
        })),
        p,
    )
}

fn parse_ty_pratt_chain(p: P, min_bp: Bp, mut seed: AstTy) -> AstTy {
    'chaining: loop {
        if match_punct(punct!('?'))
            .maybe_expect(p, bps::POST_TY_OPT.left >= min_bp)
            .is_some()
        {
            seed = AstTy {
                span: seed.span.to(p.prev_span()),
                kind: AstTyKind::Option(Box::new(seed)),
            };

            continue 'chaining;
        }

        break;
    }

    seed
}

// === Impl-like Bodies === //

fn parse_impl_ish_body(p: P) -> AstImplLikeBody {
    let Some(group) = match_group(GroupDelimiter::Brace).expect(p) else {
        p.stuck_recover_with(|_| {
            // TODO: Recover more intelligently
        });

        return AstImplLikeBody {
            span: p.next_span(),
            members: Vec::new(),
        };
    };

    let p = &mut p.enter(&group);
    let mut members = Vec::new();

    loop {
        if match_eos(p) {
            break;
        }

        members.push(parse_impl_ish_member(p));
    }

    AstImplLikeBody {
        span: group.span,
        members,
    }
}

fn parse_impl_ish_member(p: P) -> AstImplLikeMember {
    let start = p.next_span();

    let vis = parse_visibility(p);

    let make_member = |kind: AstImplLikeMemberKind, p: P| AstImplLikeMember {
        span: start.to(p.prev_span()),
        vis,
        kind,
    };

    if match_kw(kw!("type")).expect(p).is_some() {
        let Some(name) = match_ident().expect(p) else {
            return make_member(
                AstImplLikeMemberKind::Error(p.stuck_recover_with(|_| {
                    // TODO: Recover more intelligently
                })),
                p,
            );
        };

        if match_punct(punct!('=')).expect(p).is_some() {
            let ty = parse_ty(p);

            if match_punct(punct!(';')).expect(p).is_none() {
                p.stuck_recover_with(|_| {
                    // TODO: Recover more intelligently
                });
            }

            return make_member(AstImplLikeMemberKind::TypeEquals(name, ty), p);
        }

        if match_punct(punct!(':')).expect(p).is_some() {
            let clauses = parse_trait_clause_list(p);

            if match_punct(punct!(';')).expect(p).is_none() {
                p.stuck_recover_with(|_| {
                    // TODO: Recover more intelligently
                });
            }

            return make_member(AstImplLikeMemberKind::TypeInherits(name, clauses), p);
        }

        if match_punct(punct!(';')).expect(p).is_none() {
            p.stuck_recover_with(|_| {
                // TODO: Recover more intelligently
            });
        }

        return make_member(
            AstImplLikeMemberKind::TypeInherits(
                name,
                AstTraitClauseList {
                    span: Span::DUMMY,
                    clauses: Vec::new(),
                },
            ),
            p,
        );
    }

    make_member(
        AstImplLikeMemberKind::Error(p.stuck_recover_with(|c| {
            // TODO: Recover more intelligently
            c.eat();
        })),
        p,
    )
}

// === Helpers === //

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

fn match_lifetime() -> impl TokenMatcher<Output = Option<Lifetime>> {
    token_matcher(symbol!("lifetime"), |c, _| {
        c.eat().and_then(|v| v.lifetime()).copied()
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

fn parse_delimited_until_terminator<C: ?Sized, E>(
    p: P,
    cx: &mut C,
    mut match_elem: impl FnMut(P, &mut C) -> E,
    mut match_delimiter: impl FnMut(P, &mut C) -> bool,
    mut match_terminator: impl FnMut(P, &mut C) -> bool,
) -> Delimited<E> {
    let mut elems = Vec::new();

    let trailing = loop {
        if match_terminator(p, cx) {
            break !elems.is_empty();
        }

        elems.push(match_elem(p, cx));

        if match_terminator(p, cx) {
            break false;
        }

        if !match_delimiter(p, cx) {
            if !match_terminator(p, cx) {
                // Recovery strategy: ignore.
                p.stuck_recover_with(|_| {});
            }

            break false;
        }
    };

    Delimited { elems, trailing }
}

fn parse_comma_group<E>(p: P, mut match_elem: impl FnMut(P) -> E) -> Delimited<E> {
    parse_delimited_until_terminator(
        p,
        &mut (),
        |p, _| match_elem(p),
        |p, _| match_punct(punct!(',')).expect(p).is_some(),
        |p, _| match_eos(p),
    )
}

// === Binding Powers === //

pub mod bps {
    use crate::base::syntax::{PostfixBp, PrefixBp};

    pub const PRE_TY_REF: PrefixBp = PrefixBp::new(2);
    pub const POST_TY_OPT: PostfixBp = PostfixBp::new(1);
}
