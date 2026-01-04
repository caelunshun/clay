use crate::{
    base::{
        ErrorGuaranteed,
        syntax::{Bp, Matcher as _},
    },
    kw,
    parse::{
        ast::{
            AstGenericParam, AstGenericParamKind, AstGenericParamList, AstHrtbBinder, AstNamedSpec,
            AstReturnTy, AstTraitClause, AstTraitClauseList, AstTraitImplClause, AstTy, AstTyKind,
            basic::{parse_bare_path, parse_mutability},
            bp::ty_bp,
            entry::P,
            utils::{
                match_group, match_ident, match_kw, match_lifetime, match_punct, match_punct_seq,
                parse_comma_group, parse_delimited_until_terminator,
            },
        },
        token::GroupDelimiter,
    },
    punct, puncts, symbol,
};

// === Trait Clauses === //

pub fn parse_trait_clause_list(p: P) -> AstTraitClauseList {
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

pub fn parse_trait_clause(p: P) -> Result<AstTraitClause, ErrorGuaranteed> {
    if let Some(lifetime) = match_lifetime().expect(p) {
        return Ok(AstTraitClause::Outlives(lifetime));
    }

    let start = p.next_span();
    let binder = parse_hrtb_binder(p);

    if let Some(spec) = parse_named_spec(p) {
        return Ok(AstTraitClause::Trait(AstTraitImplClause {
            span: start.to(p.prev_span()),
            binder,
            spec,
        }));
    }

    Err(p.stuck().error())
}

pub fn parse_named_spec(p: P) -> Option<AstNamedSpec> {
    let start = p.next_span();

    let path = parse_bare_path(p)?;

    let params = parse_generic_param_list(p);

    Some(AstNamedSpec {
        span: start.to(p.prev_span()),
        path,
        params,
    })
}

pub fn parse_hrtb_binder(p: P) -> Option<AstHrtbBinder> {
    let start = p.next_span();

    if match_kw(kw!("for")).expect(p).is_none() {
        return None;
    }

    let Some(params) = parse_generic_param_list(p) else {
        p.stuck().ignore_not_in_loop();
        return None;
    };

    Some(AstHrtbBinder {
        span: start.to(p.prev_span()),
        params,
    })
}

// === Generic Parameters === //

pub fn parse_generic_param_list(p: P) -> Option<AstGenericParamList> {
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

pub fn parse_generic_param(p: P) -> AstGenericParam {
    let start = p.next_span();

    if let Some(path) = parse_bare_path(p) {
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

pub fn parse_ty(p: P) -> AstTy {
    parse_ty_pratt(p, Bp::MIN)
}

pub fn parse_ty_pratt(p: P, min_bp: Bp) -> AstTy {
    let seed = parse_ty_pratt_seed(p);

    parse_ty_pratt_chain(p, min_bp, seed)
}

pub fn parse_ty_pratt_seed(p: P) -> AstTy {
    let mut p = p.to_parse_guard(symbol!("type"));
    let p = &mut p;

    let seed_start = p.next_span();
    let build_ty = move |kind: AstTyKind, p: P| AstTy {
        span: seed_start.to(p.prev_span()),
        kind,
    };

    // Parse self
    if match_kw(kw!("Self")).expect(p).is_some() {
        return build_ty(AstTyKind::This, p);
    }

    // Parse path
    if let Some(path) = parse_bare_path(p) {
        return build_ty(AstTyKind::Name(path, parse_generic_param_list(p)), p);
    }

    // Parse `dyn` trait
    if match_kw(kw!("dyn")).expect(p).is_some() {
        return build_ty(AstTyKind::Trait(parse_trait_clause_list(p)), p);
    }

    // Parse reference
    if match_punct(punct!('&')).expect(p).is_some() {
        return build_ty(
            AstTyKind::Reference(
                match_lifetime().expect(p),
                parse_mutability(p),
                Box::new(parse_ty_pratt(p, ty_bp::PRE_TY_REF.right)),
            ),
            p,
        );
    }

    // Parse tuple
    if let Some(group) = match_group(GroupDelimiter::Paren).expect(p) {
        let parts = parse_comma_group(&mut p.enter(&group), parse_ty);

        match parts.into_singleton() {
            Ok(singleton) => return build_ty(AstTyKind::Paren(Box::new(singleton)), p),
            Err(parts) => return build_ty(AstTyKind::Tuple(parts), p),
        }
    }

    // Parse infer
    if match_kw(kw!("_")).expect(p).is_some() {
        return build_ty(AstTyKind::Infer, p);
    }

    // Parse projection
    if match_punct(punct!('<')).expect(p).is_some() {
        let target = parse_ty(p);

        if match_kw(kw!("as")).expect(p).is_none() {
            return build_ty(AstTyKind::Error(p.stuck().error()), p);
        }

        let Some(spec) = parse_named_spec(p) else {
            return build_ty(AstTyKind::Error(p.stuck().error()), p);
        };

        if match_punct(punct!('>')).expect(p).is_none() {
            return build_ty(AstTyKind::Error(p.stuck().error()), p);
        }

        if match_punct_seq(puncts!("::")).expect(p).is_none() {
            return build_ty(AstTyKind::Error(p.stuck().error()), p);
        }

        let Some(assoc) = match_ident().expect(p) else {
            return build_ty(AstTyKind::Error(p.stuck().error()), p);
        };

        return build_ty(
            AstTyKind::Project(Box::new(target), Box::new(spec), assoc),
            p,
        );
    }

    build_ty(AstTyKind::Error(p.stuck().error()), p)
}

pub fn parse_ty_pratt_chain(p: P, min_bp: Bp, seed: AstTy) -> AstTy {
    _ = (p, min_bp);
    seed
}

pub fn parse_return_ty(p: P) -> AstReturnTy {
    if match_punct_seq(puncts!("->")).expect(p).is_none() {
        return AstReturnTy::Omitted;
    }

    AstReturnTy::Present(parse_ty(p))
}
