use crate::{
    base::{
        Diag, ErrorGuaranteed, LeafDiag, Level, Session,
        arena::Obj,
        syntax::{HasSpan as _, Span},
    },
    parse::ast::{AstOptMutability, AstPat, AstPatFieldKind, AstPatKind},
    semantic::{
        lower::{entry::IntraItemLowerCtxt, func::path::ExprPathIdentOrResolution},
        syntax::{
            HirLocal, HirPat, HirPatKind, HirPatListFrontAndTail, HirPatNamedField, LocalNameIdent,
            LocalNameSymbol, Mutability,
        },
    },
    utils::hash::FxHashMap,
};
use std::{cell::Cell, fmt, mem};

// === Fork Resolution === //

#[derive(Debug)]
pub struct PatLocalBranchResolver<'a> {
    locals: &'a mut FxHashMap<LocalNameSymbol, PatLocal>,
    case_mention_stack: &'a mut Vec<LocalNameSymbol>,
    should_use_case_mention_stack: bool,
}

#[derive(Debug)]
struct PatLocal {
    currently_bound_at: Option<Span>,
    original_binder_span: Span,
    local: Obj<HirLocal>,
}

impl PatLocalBranchResolver<'_> {
    pub fn start<R>(f: impl FnOnce(&mut PatLocalBranchResolver<'_>) -> R) -> R {
        f(&mut PatLocalBranchResolver {
            locals: &mut FxHashMap::default(),
            case_mention_stack: &mut Vec::new(),
            should_use_case_mention_stack: false,
        })
    }

    pub fn fork<R>(
        &mut self,
        f: impl FnOnce(&mut PatLocalForkResolver<'_>) -> R,
    ) -> Result<R, ErrorGuaranteed> {
        let mut resolver = PatLocalForkResolver {
            locals: self.locals,
            case_mention_stack: self.case_mention_stack,
            fork_locals: FxHashMap::default(),
            fork_spans: Vec::new(),
            fork_had_errors: false,
        };

        let res = f(&mut resolver);

        if !resolver.fork_had_errors {
            return Ok(res);
        }

        let mut err = None;

        for (name, entry) in resolver.fork_locals {
            let Some(missing_in) = entry.missing_in else {
                continue;
            };

            let mut diag = Diag::anon_err(format_args!(
                "identifier `{name}` not bound in all patterns"
            ))
            .primary(entry.first_bound_in, "variable not in all patterns");

            for missing_in in missing_in {
                diag.push_secondary(
                    resolver.fork_spans[missing_in as usize],
                    format_args!("pattern doesn't bind `{name}`"),
                );
            }

            err = Some(diag.emit());
        }

        Err(err.unwrap())
    }

    pub fn resolve(
        &mut self,
        name: LocalNameIdent,
        mutability: Mutability,
        s: &Session,
    ) -> Result<Obj<HirLocal>, ErrorGuaranteed> {
        let local = match self.locals.entry(name.as_symbol()) {
            hashbrown::hash_map::Entry::Vacant(entry) => {
                let local = Obj::new(HirLocal { mutability, name }, s);

                entry.insert(PatLocal {
                    currently_bound_at: Some(name.span()),
                    original_binder_span: name.span(),
                    local,
                });

                local
            }
            hashbrown::hash_map::Entry::Occupied(entry) => {
                let entry = entry.into_mut();

                if let Some(prev_binding) = entry.currently_bound_at {
                    return Err(Diag::span_err(
                        name.span(),
                        format_args!(
                            "identifier `{name}` is bound more than once in the same pattern"
                        ),
                    )
                    .child(LeafDiag::span_note(
                        prev_binding,
                        "identifier was first bound here",
                    ))
                    .emit());
                }

                if entry.local.r(s).mutability != mutability {
                    return Err(Diag::anon_err(format_args!(
                        "identifier `{name}` is bound with differing mutabilities in the same pattern"
                    ))
                    .primary(name.span(), format_args!("now bound {}", mutability.adverb()))
                    .secondary(
                        entry.original_binder_span,
                        format_args!("originally bound {}", entry.local.r(s).mutability.adverb()),
                    )
                    .emit());
                }

                entry.currently_bound_at = Some(name.span());

                entry.local
            }
        };

        if self.should_use_case_mention_stack {
            self.case_mention_stack.push(name.as_symbol());
        }

        Ok(local)
    }
}

#[derive(Debug)]
pub struct PatLocalForkResolver<'a> {
    locals: &'a mut FxHashMap<LocalNameSymbol, PatLocal>,
    case_mention_stack: &'a mut Vec<LocalNameSymbol>,
    fork_locals: FxHashMap<LocalNameSymbol, ForkLocalState>,
    fork_spans: Vec<Span>,
    fork_had_errors: bool,
}

#[derive(Debug)]
struct ForkLocalState {
    first_bound_in: Span,
    tmp_bound_in_curr_fork: bool,
    missing_in: Option<Vec<u32>>,
}

impl PatLocalForkResolver<'_> {
    pub fn case<R>(
        &mut self,
        span: Span,
        f: impl FnOnce(&mut PatLocalBranchResolver<'_>) -> R,
    ) -> R {
        let fork_idx = self.fork_spans.len() as u32;
        self.fork_spans.push(span);

        let old_mention_stack_len = self.case_mention_stack.len();

        let res = f(&mut PatLocalBranchResolver {
            locals: self.locals,
            case_mention_stack: self.case_mention_stack,
            should_use_case_mention_stack: true,
        });

        // Mark all mentioned locals as being `tmp_bound_in_curr_fork`.
        for mention in self.case_mention_stack.drain(old_mention_stack_len..) {
            match self.fork_locals.entry(mention) {
                hashbrown::hash_map::Entry::Vacant(entry) => {
                    if fork_idx == 0 {
                        // We're properly bound in all forks.
                        entry.insert(ForkLocalState {
                            first_bound_in: span,
                            tmp_bound_in_curr_fork: true,
                            missing_in: None,
                        });
                    } else {
                        // We've been missing in forks up until now.
                        entry.insert(ForkLocalState {
                            first_bound_in: span,
                            tmp_bound_in_curr_fork: true,
                            missing_in: Some((0..fork_idx).collect()),
                        });

                        self.fork_had_errors = true;
                    }
                }
                hashbrown::hash_map::Entry::Occupied(entry) => {
                    entry.into_mut().tmp_bound_in_curr_fork = true;
                }
            }

            self.locals.get_mut(&mention).unwrap().currently_bound_at = None;
        }

        // Write down errors for locals not bound in the current fork.
        for entry in self.fork_locals.values_mut() {
            if mem::take(&mut entry.tmp_bound_in_curr_fork) {
                continue;
            }

            self.fork_had_errors = true;
            entry.missing_in.get_or_insert_default().push(fork_idx);
        }

        res
    }
}

// === Lowering === //

#[derive(Debug, Copy, Clone)]
pub enum PatLowerContext<'a> {
    Body,
    FnSigFirstToplevel(&'a Cell<bool>),
    FnSigFirstNested,
    FnSigSubsequent,
}

impl PatLowerContext<'_> {
    pub fn move_inwards(self) -> Self {
        match self {
            PatLowerContext::Body
            | PatLowerContext::FnSigFirstNested
            | PatLowerContext::FnSigSubsequent => self,
            PatLowerContext::FnSigFirstToplevel(_) => PatLowerContext::FnSigFirstNested,
        }
    }
}

impl IntraItemLowerCtxt<'_> {
    pub fn lower_pat(&mut self, ast: &AstPat) -> Obj<HirPat> {
        PatLocalBranchResolver::start(|locals| {
            self.lower_pat_inner(ast, locals, PatLowerContext::Body)
        })
    }

    pub fn lower_pat_inner(
        &mut self,
        ast: &AstPat,
        locals: &mut PatLocalBranchResolver,
        cx: PatLowerContext,
    ) -> Obj<HirPat> {
        let tcx = self.tcx;
        let s = &self.tcx.session;

        let kind = match &ast.kind {
            AstPatKind::Hole => HirPatKind::Hole,
            AstPatKind::Path {
                binding_mode,
                path,
                and_bind,
            } => 'path: {
                let res = self.resolve_expr_path(path);

                match res.as_ident_or_res(path, s) {
                    Ok(ExprPathIdentOrResolution::Ident(name)) => {
                        match name {
                            LocalNameIdent::SelfName(span) => match cx {
                                PatLowerContext::Body => {
                                    // (fallthrough)
                                }
                                PatLowerContext::FnSigFirstToplevel(self_param_span) => {
                                    self_param_span.set(true);
                                }
                                PatLowerContext::FnSigFirstNested => {
                                    Diag::span_err(
                                        span,
                                        "`self` can only appear at the top-level of the first \
                                         argument's pattern in the function signature",
                                    )
                                    .emit();
                                }
                                PatLowerContext::FnSigSubsequent => {
                                    Diag::span_err(
                                        span,
                                        "`self` can only appear in the first argument of a function's \
                                         signature",
                                    )
                                    .emit();
                                }
                            },
                            LocalNameIdent::User(_name) => {
                                // (fallthrough)
                            }
                        }

                        match locals.resolve(name, binding_mode.local_muta.as_muta(), s) {
                            Ok(local) => {
                                self.func_local_names
                                    .define_force_shadow(name.as_symbol(), local);

                                HirPatKind::Binding(
                                    binding_mode.by_ref,
                                    local,
                                    and_bind.as_ref().map(|ast| {
                                        self.lower_pat_inner(ast, locals, cx.move_inwards())
                                    }),
                                )
                            }
                            Err(err) => HirPatKind::Error(err),
                        }
                    }
                    Ok(ExprPathIdentOrResolution::Resolution(res)) => {
                        let Some(ctor) = res.as_adt(path, tcx) else {
                            break 'path HirPatKind::Error(
                                Diag::span_err(
                                    path.span,
                                    format_args!("expected pattern, got {}", res.bare_what(s)),
                                )
                                .emit(),
                            );
                        };

                        if let Some(and_bind) = and_bind {
                            Diag::span_err(and_bind.span, "`@` only allowed after identifier")
                                .emit();
                        }

                        HirPatKind::AdtUnit(ctor)
                    }
                    Err(err) => HirPatKind::Error(err),
                }
            }
            AstPatKind::PathAndBrace(path, fields, rest) => 'path: {
                let res = match self.resolve_expr_path(path).fail_on_unbound_local() {
                    Ok(v) => v,
                    Err(err) => break 'path HirPatKind::Error(err),
                };

                let Some(ctor) = res.as_adt(path, tcx) else {
                    break 'path HirPatKind::Error(
                        Diag::span_err(
                            path.span,
                            format_args!(
                                "expected named struct or enum variant, got {}",
                                res.bare_what(s)
                            ),
                        )
                        .emit(),
                    );
                };

                let fields = Obj::new_iter(
                    fields.iter().map(|field| match &field.kind {
                        AstPatFieldKind::WithPat(pat) => HirPatNamedField {
                            name: field.name,
                            pat: self.lower_pat_inner(pat, locals, cx.move_inwards()),
                        },
                        AstPatFieldKind::Bare(muta) => {
                            let kind = match locals.resolve(
                                LocalNameIdent::User(field.name),
                                muta.as_muta(),
                                s,
                            ) {
                                Ok(name) => {
                                    HirPatKind::Binding(AstOptMutability::Implicit, name, None)
                                }
                                Err(err) => HirPatKind::Error(err),
                            };

                            HirPatNamedField {
                                name: field.name,
                                pat: Obj::new(
                                    HirPat {
                                        span: field.name.span,
                                        kind,
                                    },
                                    s,
                                ),
                            }
                        }
                    }),
                    s,
                );

                HirPatKind::AdtNamed(ctor, fields)
            }
            AstPatKind::PathAndParen(path, children) => 'pat: {
                let res = match self.resolve_expr_path(path).fail_on_unbound_local() {
                    Ok(v) => v,
                    Err(err) => break 'pat HirPatKind::Error(err),
                };

                let Some(ctor) = res.as_adt(path, tcx) else {
                    break 'pat HirPatKind::Error(
                        Diag::span_err(
                            path.span,
                            format_args!(
                                "expected tuple struct or enum variant, got {}",
                                res.bare_what(s)
                            ),
                        )
                        .emit(),
                    );
                };

                let children = self.lower_pat_list_front_and_tail(
                    "tuple",
                    children,
                    locals,
                    cx.move_inwards(),
                );

                HirPatKind::AdtTuple(ctor, children)
            }
            AstPatKind::Or(pats) => {
                match locals.fork(|locals| {
                    let mut forks = Vec::new();

                    for pat in pats {
                        forks.push(locals.case(pat.span, |locals| {
                            self.lower_pat_inner(pat, locals, cx.move_inwards())
                        }));
                    }

                    Obj::new_slice(&forks, s)
                }) {
                    Ok(forks) => HirPatKind::Or(forks),
                    Err(err) => HirPatKind::Error(err),
                }
            }
            AstPatKind::Tuple(pats) => HirPatKind::Tuple(self.lower_pat_list_front_and_tail(
                "tuple",
                pats,
                locals,
                cx.move_inwards(),
            )),
            AstPatKind::Paren(pat) => return self.lower_pat(pat),
            AstPatKind::Ref(muta, inner) => HirPatKind::Deref(
                muta.as_muta(),
                self.lower_pat_inner(inner, locals, cx.move_inwards()),
            ),
            AstPatKind::Slice(pats) => HirPatKind::Slice(self.lower_pat_list_front_and_tail(
                "slice",
                pats,
                locals,
                cx.move_inwards(),
            )),
            AstPatKind::Rest => HirPatKind::Error(
                Diag::span_err(ast.span, "`..` patterns are not allowed here")
                    .child(LeafDiag::new(
                        Level::Note,
                        "only allowed in tuple, tuple struct, and slice patterns",
                    ))
                    .emit(),
            ),
            AstPatKind::Range(inner) => HirPatKind::Range(self.lower_range_expr(ast.span, inner)),
            AstPatKind::Lit(expr) => HirPatKind::Lit(self.lower_expr(expr)),
            AstPatKind::Error(err) => HirPatKind::Error(*err),
        };

        Obj::new(
            HirPat {
                span: ast.span,
                kind,
            },
            s,
        )
    }

    pub fn lower_pat_list_front_and_tail_generic<T>(
        &mut self,
        kind_name: impl fmt::Display,
        list: impl IntoIterator<Item = T>,
        mut lower: impl FnMut(&mut Self, T) -> PatOrRest,
    ) -> HirPatListFrontAndTail {
        let s = &self.tcx.session;

        let mut found_rest = None;

        let mut front = Vec::new();
        let mut tail = Vec::new();

        for item in list {
            match lower(self, item) {
                PatOrRest::Pat(pat) => {
                    if found_rest.is_some() {
                        tail.push(pat);
                    } else {
                        front.push(pat);
                    }
                }
                PatOrRest::Rest(new_span) => {
                    if let Some(prev_span) = found_rest {
                        Diag::anon_err(format_args!(
                            "`..` can only be used once per {kind_name} pattern"
                        ))
                        .primary(
                            new_span,
                            format_args!("can only be used once per {kind_name} pattern"),
                        )
                        .secondary(prev_span, "previously used here")
                        .emit();
                    } else {
                        found_rest = Some(new_span);
                    }
                }
            }
        }

        HirPatListFrontAndTail {
            front: Obj::new_slice(&front, s),
            tail: found_rest.map(|_| Obj::new_slice(&tail, s)),
        }
    }

    pub fn lower_pat_list_front_and_tail(
        &mut self,
        kind_name: impl fmt::Display,
        asts: &[AstPat],
        locals: &mut PatLocalBranchResolver,
        cx: PatLowerContext,
    ) -> HirPatListFrontAndTail {
        self.lower_pat_list_front_and_tail_generic(kind_name, asts, |this, ast| match &ast.kind {
            AstPatKind::Rest => PatOrRest::Rest(ast.span),
            _ => PatOrRest::Pat(this.lower_pat_inner(ast, locals, cx.move_inwards())),
        })
    }
}

#[derive(Debug, Copy, Clone)]
pub enum PatOrRest {
    Pat(Obj<HirPat>),
    Rest(Span),
}
