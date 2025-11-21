use crate::{
    base::syntax::Matcher as _,
    kw,
    parse::{
        ast::{
            AstAttribute, AstExprPath, AstExprPathSegment, AstOptMutability, AstSimplePath,
            AstUsePath, AstUsePathKind, AstVisibility, AstVisibilityKind,
            entry::P,
            types::parse_generic_param_list,
            utils::{
                match_eos, match_group, match_ident, match_kw, match_punct, match_punct_seq,
                parse_delimited_until_terminator,
            },
        },
        token::{GroupDelimiter, Ident},
    },
    punct, puncts, symbol,
};
use std::rc::Rc;

pub fn parse_attributes(p: P) -> Vec<AstAttribute> {
    let mut attrs = Vec::new();

    while let Some(attr) = parse_attribute(p) {
        attrs.push(attr);
    }

    attrs
}

pub fn parse_attribute(p: P) -> Option<AstAttribute> {
    let start = p.next_span();

    let mut p = p.to_parse_guard(symbol!("attribute"));
    let p = &mut p;

    match_punct(punct!('#')).expect(p)?;

    let is_inner = match_punct(punct!('!')).expect(p).is_some();

    let Some(bracket) = match_group(GroupDelimiter::Bracket).expect(p) else {
        p.stuck().ignore_not_in_loop();
        return None;
    };

    let mut p2 = p.enter(&bracket);

    let Some(path) = parse_simple_path(&mut p2) else {
        p2.stuck().ignore_not_in_loop();
        return None;
    };

    let Some(paren) = match_group(GroupDelimiter::Paren).expect(&mut p2) else {
        p2.stuck().ignore_not_in_loop();
        return None;
    };

    if !match_eos(&mut p2) {
        p2.stuck().ignore_not_in_loop();
        return None;
    }

    Some(AstAttribute {
        span: start.to(p.prev_span()),
        is_inner,
        path,
        args: paren.tokens,
    })
}

pub fn parse_simple_path(p: P) -> Option<AstSimplePath> {
    let start = p.next_span();

    let mut p = p.to_parse_guard(symbol!("path"));
    let p = &mut p;

    let mut parts = Vec::new();

    loop {
        let Some(part) = parse_path_part(p) else {
            if !parts.is_empty() {
                p.stuck().ignore_about_to_break();
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

pub fn parse_path_part(p: P) -> Option<Ident> {
    let mut p = p.to_parse_guard(symbol!("path part"));
    let p = &mut p;

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

pub fn parse_use_path(p: P) -> Option<AstUsePath> {
    let start = p.next_span();

    let mut p = p.to_parse_guard(symbol!("path"));
    let p = &mut p;

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
            |p, ()| parse_use_path(p),
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

    p.stuck().ignore_not_in_loop();

    Some(AstUsePath {
        span: start.to(p.prev_span()),
        base: Rc::from(parts),
        kind: AstUsePathKind::Direct(None),
    })
}

pub fn parse_expr_path(p: P) -> Option<AstExprPath> {
    let start = p.next_span();

    let mut p = p.to_parse_guard(symbol!("path"));
    let p = &mut p;

    let mut parts = Vec::new();

    loop {
        let Some(part) = parse_path_part(p) else {
            if !parts.is_empty() {
                p.stuck().ignore_about_to_break();
            }

            break;
        };

        if match_punct_seq(puncts!("::")).expect(p).is_none() {
            parts.push(AstExprPathSegment { part, args: None });
            break;
        }

        let args = parse_generic_param_list(p).map(Box::new);
        let args_is_some = args.is_some();

        parts.push(AstExprPathSegment { part, args });

        if args_is_some && match_punct_seq(puncts!("::")).expect(p).is_none() {
            break;
        }
    }

    if parts.is_empty() {
        return None;
    }

    Some(AstExprPath {
        span: start.to(p.prev_span()),
        segments: Rc::from(parts),
    })
}

pub fn parse_mutability(p: P) -> AstOptMutability {
    let mut p = p.to_parse_guard(symbol!("mutability"));
    let p = &mut p;

    if let Some(kw) = match_kw(kw!("mut")).expect(p) {
        return AstOptMutability::Mut(kw.span);
    }

    if let Some(kw) = match_kw(kw!("ref")).expect(p) {
        return AstOptMutability::Ref(kw.span);
    }

    AstOptMutability::Implicit
}

pub fn parse_visibility(p: P) -> AstVisibility {
    let mut p = p.to_parse_guard(symbol!("visibility"));
    let p = &mut *p;

    let start = p.next_span();

    if match_kw(kw!("pub")).expect(p).is_some() {
        if let Some(group) = match_group(GroupDelimiter::Paren).expect(p) {
            let mut p2 = p.enter(&group);

            let Some(path) = parse_simple_path(&mut p2) else {
                p2.stuck().ignore_not_in_loop();

                return AstVisibility {
                    span: start.to(p.prev_span()),
                    kind: AstVisibilityKind::Pub,
                };
            };

            if !match_eos(&mut p2) {
                p2.stuck().ignore_not_in_loop();
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
