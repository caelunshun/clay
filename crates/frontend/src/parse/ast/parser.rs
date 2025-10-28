use crate::{
    base::{
        ErrorGuaranteed, LeafDiag, Level, Session,
        syntax::{Matcher as _, Span},
    },
    kw,
    parse::{
        ast::{
            AstAttribute, AstGenericDef, AstGenericDefKind, AstGenericDefList, AstItem,
            AstItemKind, AstItemModule, AstItemModuleContents, AstItemTrait, AstSimplePath,
            AstTraitClause, AstTraitClauseKind, AstTraitClauseList, AstTraitParam, AstVisibility,
            AstVisibilityKind, Keyword, PunctSeq,
        },
        token::{
            GroupDelimiter, Ident, Lifetime, Punct, TokenCharLit, TokenCursor, TokenGroup,
            TokenMatcher, TokenNumLit, TokenParser, TokenPunct, TokenStrLit, token_matcher,
        },
    },
    punct, puncts, symbol,
};
use std::rc::Rc;

// === Items === //

type P<'a, 'g> = &'a mut TokenParser<'g>;
type C<'a, 'g> = &'a mut TokenCursor<'g>;

pub fn parse_file(tokens: &TokenGroup) -> AstItemModuleContents {
    let mut p = TokenParser::new(tokens);

    parse_mod_contents(&mut p)
}

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

        let generics = parse_generic_def_list(p);

        return Some(make_item(
            AstItemKind::Trait(AstItemTrait {
                name,
                generics,
                // TODO: parse members
                members: Vec::new(),
            }),
            p,
        ));
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

// === Type Parsing === //

fn parse_generic_def_list(p: P) -> Option<AstGenericDefList> {
    let start = match_punct(punct!('<')).expect(p)?;

    let defs = parse_delimited_until_terminator(
        p,
        &mut (),
        |p, ()| parse_generic_def(p),
        |p, ()| match_punct(punct!(',')).expect(p).is_some(),
        |p, ()| match_punct(punct!('>')).expect(p).is_some(),
    );

    Some(AstGenericDefList {
        span: start.span.to(p.prev_span()),
        defs: defs.elems,
    })
}

fn parse_generic_def(p: P) -> Result<AstGenericDef, ErrorGuaranteed> {
    let start = p.next_span();

    let kind = 'kind: {
        if let Some(name) = match_ident().expect(p) {
            break 'kind AstGenericDefKind::Type(name);
        }

        if let Some(name) = match_lifetime().expect(p) {
            break 'kind AstGenericDefKind::Lifetime(name);
        }

        return Err(p.stuck_recover_with(|_| {
            // TODO: Recover more intelligently
        }));
    };

    if match_punct(punct!(':')).expect(p).is_none() {
        return Ok(AstGenericDef {
            span: start.to(p.prev_span()),
            kind,
            clauses: None,
        });
    }

    let clauses = parse_trait_clause_list(p);

    Ok(AstGenericDef {
        span: start.to(p.prev_span()),
        kind,
        clauses: Some(clauses),
    })
}

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
        return Ok(AstTraitClause {
            span: start.to(p.prev_span()),
            kind: AstTraitClauseKind::Outlives(lifetime),
        });
    }

    if let Some(path) = parse_simple_path(p) {
        let params = parse_trait_param_list(p);

        return Ok(AstTraitClause {
            span: start.to(p.prev_span()),
            kind: AstTraitClauseKind::Trait(path, params),
        });
    }

    Err(p.stuck_recover_with(|_| {
        // TODO: Recover more intelligently
    }))
}

fn parse_trait_param_list(p: P) -> Vec<AstTraitParam> {
    if match_punct(punct!('<')).expect(p).is_none() {
        return Vec::new();
    }

    parse_delimited_until_terminator(
        p,
        &mut (),
        |p, ()| parse_trait_param(p),
        |p, ()| match_punct(punct!(',')).expect(p).is_some(),
        |p, ()| match_punct(punct!('>')).expect(p).is_some(),
    )
    .elems
}

fn parse_trait_param(p: P) -> AstTraitParam {
    todo!();
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
