use crate::{
    base::{
        ErrorGuaranteed,
        syntax::{Bp, Matcher as _},
    },
    kw,
    parse::{
        ast::{
            AstFnArg, AstFnDef, AstPat, AstPatKind,
            entry::P,
            types::{parse_generic_param_list, parse_return_ty, parse_ty},
            utils::{match_group, match_ident, match_kw, match_punct, parse_comma_group},
        },
        token::GroupDelimiter,
    },
    punct,
};

// === Functions === //

pub fn parse_func(p: P) -> Result<Option<AstFnDef>, ErrorGuaranteed> {
    let start = p.next_span();

    if match_kw(kw!("fn")).expect(p).is_none() {
        return Ok(None);
    }

    let Some(name) = match_ident().expect(p) else {
        return Err(p.stuck());
    };

    let generics = parse_generic_param_list(p);

    let Some(params) = match_group(GroupDelimiter::Paren).expect(p) else {
        return Err(p.stuck());
    };

    let args = parse_comma_group(&mut p.enter(&params), parse_func_arg).elems;

    let ret_ty = parse_return_ty(p);

    // TODO: Body

    Ok(Some(AstFnDef {
        span: start.to(p.prev_span()),
        name,
        generics,
        args,
        ret_ty,
        body: None,
    }))
}

pub fn parse_func_arg(p: P) -> AstFnArg {
    let start = p.next_span();

    let pat = parse_pat(p);

    if match_punct(punct!(':')).expect(p).is_none() {
        p.stuck();
    }

    let ty = parse_ty(p);

    AstFnArg {
        span: start.to(p.prev_span()),
        pat: Box::new(pat),
        ty: Box::new(ty),
    }
}

// === Expressions === //

// TODO

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

    build_pat(AstPatKind::Error(p.stuck()), p)
}

pub fn parse_pat_pratt_chain(p: P, min_bp: Bp, mut seed: AstPat) -> AstPat {
    todo!()
}
