use crate::{
    base::syntax::{Matcher as _, Span},
    kw,
    parse::{
        ast::{
            AstAttribute, AstEnumVariant, AstImplLikeBody, AstImplLikeMember,
            AstImplLikeMemberKind, AstItem, AstItemBase, AstItemEnum, AstItemFn, AstItemImpl,
            AstItemModule, AstItemModuleContents, AstItemStruct, AstItemTrait, AstItemTypeAlias,
            AstItemUse, AstStructAnonField, AstStructKind, AstStructNamedField, AstTraitClauseList,
            basic::{parse_attributes, parse_tree_path, parse_visibility},
            entry::P,
            func::parse_func,
            types::{parse_generic_param_list, parse_trait_clause_list, parse_ty},
            utils::{
                match_eos, match_group, match_ident, match_kw, match_punct, parse_comma_group,
            },
        },
        token::{GroupDelimiter, TokenParser},
    },
    punct, symbol,
};

pub fn parse_mod_contents(p: P) -> AstItemModuleContents {
    let mut inner_attrs = Vec::new();
    let mut items = Vec::new();

    loop {
        p.recover_until(|c| {
            [
                kw!("pub"),
                kw!("priv"),
                kw!("struct"),
                kw!("enum"),
                kw!("use"),
                kw!("mod"),
                kw!("fn"),
            ]
            .into_iter()
            .any(|k| match_kw(k).consume(c).is_some())
        });

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

        if p.stuck().should_break() {
            break;
        }
    }

    AstItemModuleContents { inner_attrs, items }
}

fn parse_item(p: P, outer_attrs: Vec<AstAttribute>) -> Option<AstItem> {
    let start = p.next_span();

    let vis = parse_visibility(p);

    let uncommitted = outer_attrs.is_empty() && vis.kind.is_omitted();

    let make_base = |p: &mut TokenParser| AstItemBase {
        span: start.to(p.prev_span()),
        outer_attrs,
        vis,
    };

    let mut p = p.to_parse_guard(symbol!("item"));
    let p = &mut *p;

    if match_kw(kw!("mod")).expect(p).is_some() {
        let Some(name) = match_ident().expect_to_parse(p, symbol!("module name")) else {
            return Some(AstItem::Error(make_base(p), p.stuck().error()));
        };

        if let Some(group) = match_group(GroupDelimiter::Brace).expect(p) {
            return Some(AstItem::Mod(AstItemModule {
                name,
                contents: Some(parse_mod_contents(&mut p.enter(&group))),
                base: make_base(p),
            }));
        } else {
            if match_punct(punct!(';')).expect(p).is_none() {
                p.stuck().ignore_not_in_loop();
            }

            return Some(AstItem::Mod(AstItemModule {
                name,
                contents: None,
                base: make_base(p),
            }));
        }
    }

    if match_kw(kw!("type")).expect(p).is_some() {
        let Some(name) = match_ident().expect_to_parse(p, symbol!("type name")) else {
            return Some(AstItem::Error(make_base(p), p.stuck().error()));
        };

        let generics = parse_generic_param_list(p);

        if match_punct(punct!('=')).expect(p).is_none() {
            p.stuck().ignore_not_in_loop();
        }

        let body = Box::new(parse_ty(p));

        if match_punct(punct!(';')).expect(p).is_none() {
            p.stuck().ignore_not_in_loop();
        }

        return Some(AstItem::TypeAlias(AstItemTypeAlias {
            name,
            generics,
            body,
            base: make_base(p),
        }));
    }

    if match_kw(kw!("trait")).expect(p).is_some() {
        let Some(name) = match_ident().expect_to_parse(p, symbol!("trait name")) else {
            return Some(AstItem::Error(make_base(p), p.stuck().error()));
        };

        let generics = parse_generic_param_list(p);
        let inherits = match_punct(punct!(':'))
            .expect(p)
            .map(|_| parse_trait_clause_list(p));

        let body = parse_impl_ish_body(p);

        return Some(AstItem::Trait(AstItemTrait {
            name,
            generics,
            inherits,
            body,
            base: make_base(p),
        }));
    }

    if match_kw(kw!("impl")).expect(p).is_some() {
        let generics = parse_generic_param_list(p);

        let first_ty = parse_ty(p);
        let second_ty = match_kw(kw!("for"))
            .expect(p)
            .is_some()
            .then(|| parse_ty(p));

        let body = parse_impl_ish_body(p);

        return Some(AstItem::Impl(AstItemImpl {
            generics,
            first_ty,
            second_ty,
            body,
            base: make_base(p),
        }));
    }

    if match_kw(kw!("use")).expect(p).is_some() {
        let Some(path) = parse_tree_path(p) else {
            return Some(AstItem::Error(make_base(p), p.stuck().error()));
        };

        if match_punct(punct!(';')).expect(p).is_none() {
            p.stuck().ignore_not_in_loop();
        }

        return Some(AstItem::Use(AstItemUse {
            path,
            base: make_base(p),
        }));
    }

    if match_kw(kw!("struct")).expect(p).is_some() {
        let Some(name) = match_ident().expect_to_parse(p, symbol!("struct name")) else {
            return Some(AstItem::Error(make_base(p), p.stuck().error()));
        };

        let generics = parse_generic_param_list(p);
        let kind = parse_struct_kind(p);

        if kind.needs_semi() && match_punct(punct!(';')).expect(p).is_none() {
            p.stuck().ignore_not_in_loop();
        }

        return Some(AstItem::Struct(AstItemStruct {
            base: make_base(p),
            name,
            generics,
            kind,
        }));
    }

    if match_kw(kw!("enum")).expect(p).is_some() {
        let Some(name) = match_ident().expect_to_parse(p, symbol!("enum name")) else {
            return Some(AstItem::Error(make_base(p), p.stuck().error()));
        };

        let generics = parse_generic_param_list(p);

        let Some(group) = match_group(GroupDelimiter::Brace).expect(p) else {
            return Some(AstItem::Error(make_base(p), p.stuck().error()));
        };

        let variants = parse_comma_group(&mut p.enter(&group), |p| {
            let start = p.next_span();

            let Some(name) = match_ident().expect(p) else {
                return Err(p.stuck().error());
            };

            let kind = parse_struct_kind(p);

            Ok(AstEnumVariant {
                span: start.to(p.prev_span()),
                name,
                kind,
            })
        })
        .elems
        .into_iter()
        .filter_map(Result::ok)
        .collect();

        return Some(AstItem::Enum(AstItemEnum {
            base: make_base(p),
            name,
            generics,
            variants,
        }));
    }

    match parse_func(p) {
        Ok(Some(def)) => {
            return Some(AstItem::Func(AstItemFn {
                base: make_base(p),
                def,
            }));
        }
        Ok(None) => {
            // (fallthrough)
        }
        Err(error) => {
            return Some(AstItem::Error(make_base(p), error));
        }
    }

    if !uncommitted {
        return Some(AstItem::Error(make_base(p), p.stuck().error()));
    }

    None
}

pub fn parse_impl_ish_body(p: P) -> AstImplLikeBody {
    let Some(group) = match_group(GroupDelimiter::Brace).expect(p) else {
        p.stuck().ignore_not_in_loop();

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

        if let Some(member) = parse_impl_ish_member(p) {
            members.push(member);
            continue;
        }

        if p.stuck().should_break() {
            break;
        }
    }

    AstImplLikeBody {
        span: group.span,
        members,
    }
}

pub fn parse_impl_ish_member(p: P) -> Option<AstImplLikeMember> {
    let start = p.next_span();

    let vis = parse_visibility(p);

    let make_member = |kind: AstImplLikeMemberKind, p: P| {
        Some(AstImplLikeMember {
            span: start.to(p.prev_span()),
            vis,
            kind,
        })
    };

    if match_kw(kw!("type")).expect(p).is_some() {
        let Some(name) = match_ident().expect(p) else {
            return make_member(AstImplLikeMemberKind::Error(p.stuck().error()), p);
        };

        if match_punct(punct!('=')).expect(p).is_some() {
            let ty = parse_ty(p);

            if match_punct(punct!(';')).expect(p).is_none() {
                p.stuck().ignore_not_in_loop();
            }

            return make_member(AstImplLikeMemberKind::TypeEquals(name, ty), p);
        }

        if match_punct(punct!(':')).expect(p).is_some() {
            let clauses = parse_trait_clause_list(p);

            if match_punct(punct!(';')).expect(p).is_none() {
                p.stuck().ignore_not_in_loop();
            }

            return make_member(AstImplLikeMemberKind::TypeInherits(name, clauses), p);
        }

        if match_punct(punct!(';')).expect(p).is_none() {
            p.stuck().ignore_not_in_loop();
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

    match parse_func(p) {
        Ok(Some(def)) => {
            return make_member(AstImplLikeMemberKind::Func(def), p);
        }
        Ok(None) => {
            // (fallthrough)
        }
        Err(error) => {
            return make_member(AstImplLikeMemberKind::Error(error), p);
        }
    }

    None
}

pub fn parse_struct_kind(p: P) -> AstStructKind {
    if let Some(paren) = match_group(GroupDelimiter::Paren).expect(p) {
        let fields = parse_comma_group(&mut p.enter(&paren), |p| {
            let start = p.next_span();
            let vis = parse_visibility(p);
            let ty = parse_ty(p);

            AstStructAnonField {
                span: start.to(p.prev_span()),
                vis,
                ty,
            }
        });

        return AstStructKind::Tuple(fields.elems);
    }

    if let Some(paren) = match_group(GroupDelimiter::Brace).expect(p) {
        let fields = parse_comma_group(&mut p.enter(&paren), |p| {
            let start = p.next_span();

            let vis = parse_visibility(p);

            let Some(name) = match_ident().expect(p) else {
                p.stuck().ignore_not_in_loop();
                return None;
            };

            if match_punct(punct!(':')).expect(p).is_none() {
                p.stuck().ignore_not_in_loop();
                return None;
            }

            let ty = parse_ty(p);

            Some(AstStructNamedField {
                span: start.to(p.prev_span()),
                vis,
                name,
                ty,
            })
        });

        let fields = fields.elems.into_iter().flatten().collect::<Vec<_>>();

        return AstStructKind::Struct(fields);
    }

    AstStructKind::Unit
}
