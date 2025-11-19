use crate::{
    base::syntax::{Matcher as _, Span},
    kw,
    parse::{
        ast::{
            AstAttribute, AstFnItem, AstImplLikeBody, AstImplLikeMember, AstImplLikeMemberKind,
            AstItem, AstItemBase, AstItemImpl, AstItemModule, AstItemModuleContents, AstItemTrait,
            AstItemUse, AstTraitClauseList, AstVisibilityKind,
            basic::{parse_attributes, parse_use_path, parse_visibility},
            entry::P,
            func::parse_func,
            types::{parse_generic_param_list, parse_trait_clause_list, parse_ty},
            utils::{match_eos, match_group, match_ident, match_kw, match_punct},
        },
        token::{GroupDelimiter, TokenParser},
    },
    punct,
};

pub fn parse_mod_contents(p: P) -> AstItemModuleContents {
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

pub fn parse_item(p: P, outer_attrs: Vec<AstAttribute>) -> Option<AstItem> {
    let start = p.next_span();

    let vis = parse_visibility(p);

    let uncommitted = outer_attrs.is_empty() && matches!(vis.kind, AstVisibilityKind::Implicit);

    let make_base = |p: &mut TokenParser| AstItemBase {
        span: start.to(p.prev_span()),
        outer_attrs,
        vis,
    };

    if match_kw(kw!("mod")).expect(p).is_some() {
        let Some(name) = match_ident().expect(p) else {
            return Some(AstItem::Error(
                make_base(p),
                p.stuck_recover_with(|_| {
                    // TODO: Recover more intelligently
                }),
            ));
        };

        if let Some(group) = match_group(GroupDelimiter::Brace).expect(p) {
            return Some(AstItem::Mod(AstItemModule {
                name,
                contents: Some(parse_mod_contents(&mut p.enter(&group))),
                base: make_base(p),
            }));
        } else {
            if match_punct(punct!(';')).expect(p).is_none() {
                p.stuck_recover_with(|_| {});
            }

            return Some(AstItem::Mod(AstItemModule {
                name,
                contents: None,
                base: make_base(p),
            }));
        }
    }

    if match_kw(kw!("trait")).expect(p).is_some() {
        let Some(name) = match_ident().expect(p) else {
            return Some(AstItem::Error(
                make_base(p),
                p.stuck_recover_with(|_| {
                    // TODO: Recover more intelligently
                }),
            ));
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
        let Some(path) = parse_use_path(p) else {
            return Some(AstItem::Error(
                make_base(p),
                p.stuck_recover_with(|_| {
                    // TODO: Recover more intelligently
                }),
            ));
        };

        if match_punct(punct!(';')).expect(p).is_none() {
            p.stuck_recover_with(|_| {
                // TODO: Recover more intelligently
            });
        }

        return Some(AstItem::Use(AstItemUse {
            path,
            base: make_base(p),
        }));
    }

    match parse_func(p) {
        Ok(Some(def)) => {
            return Some(AstItem::Func(AstFnItem {
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
        return Some(AstItem::Error(
            make_base(p),
            p.stuck_recover_with(|_| {
                // TODO: Recover more intelligently
            }),
        ));
    }

    None
}

pub fn parse_impl_ish_body(p: P) -> AstImplLikeBody {
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

pub fn parse_impl_ish_member(p: P) -> AstImplLikeMember {
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
