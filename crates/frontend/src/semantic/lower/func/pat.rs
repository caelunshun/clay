use crate::{
    base::{
        Diag, ErrorGuaranteed, LeafDiag, Level, Session,
        arena::Obj,
        syntax::{Span, Symbol},
    },
    parse::{
        ast::{AstPat, AstPatFieldKind, AstPatKind, AstPatStructRest},
        token::Ident,
    },
    semantic::{
        lower::{
            entry::IntraItemLowerCtxt,
            func::path::{ExprPathIdentOrResolution, PathResolvedPattern},
        },
        syntax::{
            FuncLocal, Mutability, Pat, PatKind, PatListFrontAndTail, PatListFrontAndTailLen,
            PatNamedField,
        },
    },
    utils::hash::FxHashMap,
};
use std::mem;

// === Fork Resolution === //

#[derive(Debug)]
pub struct PatLocalBranchResolver<'a> {
    locals: &'a mut FxHashMap<Symbol, PatLocal>,
    case_mention_stack: &'a mut Vec<Symbol>,
    should_use_case_mention_stack: bool,
}

#[derive(Debug)]
struct PatLocal {
    currently_bound_at: Option<Span>,
    original_binder_span: Span,
    local: Obj<FuncLocal>,
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
        ident: Ident,
        mutability: Mutability,
        s: &Session,
    ) -> Result<Obj<FuncLocal>, ErrorGuaranteed> {
        let local = match self.locals.entry(ident.text) {
            hashbrown::hash_map::Entry::Vacant(entry) => {
                let local = Obj::new(
                    FuncLocal {
                        mutability,
                        name: ident,
                    },
                    s,
                );

                entry.insert(PatLocal {
                    currently_bound_at: Some(ident.span),
                    original_binder_span: ident.span,
                    local,
                });

                local
            }
            hashbrown::hash_map::Entry::Occupied(entry) => {
                let entry = entry.into_mut();

                if let Some(prev_binding) = entry.currently_bound_at {
                    return Err(Diag::span_err(
                        ident.span,
                        format_args!(
                            "identifier `{}` is bound more than once in the same pattern",
                            ident.text
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
                        "identifier `{}` is bound with differing mutabilities in the same pattern",
                        ident.text
                    ))
                    .primary(
                        ident.span,
                        format_args!("now bound {}", mutability.adverb()),
                    )
                    .secondary(
                        entry.original_binder_span,
                        format_args!("originally bound {}", entry.local.r(s).mutability.adverb()),
                    )
                    .emit());
                }

                entry.currently_bound_at = Some(ident.span);

                entry.local
            }
        };

        if self.should_use_case_mention_stack {
            self.case_mention_stack.push(ident.text);
        }

        Ok(local)
    }
}

#[derive(Debug)]
pub struct PatLocalForkResolver<'a> {
    locals: &'a mut FxHashMap<Symbol, PatLocal>,
    case_mention_stack: &'a mut Vec<Symbol>,
    fork_locals: FxHashMap<Symbol, ForkLocalState>,
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

impl IntraItemLowerCtxt<'_> {
    pub fn lower_pat(&mut self, ast: &AstPat) -> Obj<Pat> {
        PatLocalBranchResolver::start(|locals| self.lower_pat_inner(ast, locals))
    }

    fn lower_pat_inner(&mut self, ast: &AstPat, locals: &mut PatLocalBranchResolver) -> Obj<Pat> {
        let s = &self.tcx.session;

        let kind = match &ast.kind {
            AstPatKind::Hole => PatKind::Hole,
            AstPatKind::Path {
                binding_mode,
                path,
                and_bind,
            } => 'path: {
                let res = self.resolve_expr_path(path);

                match res.as_ident_or_res(path, s) {
                    Ok(ExprPathIdentOrResolution::Ident(name)) => {
                        match locals.resolve(name, binding_mode.local_muta.as_muta(), s) {
                            Ok(local) => {
                                self.func_local_names.define_force_shadow(name.text, local);

                                PatKind::NewName(
                                    local,
                                    and_bind
                                        .as_ref()
                                        .map(|ast| self.lower_pat_inner(ast, locals)),
                                )
                            }
                            Err(err) => PatKind::Error(err),
                        }
                    }
                    Ok(ExprPathIdentOrResolution::Resolution(res)) => {
                        let Some(kind) = res.as_pat(s) else {
                            break 'path PatKind::Error(
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

                        match kind {
                            PathResolvedPattern::UnitCtor(ctor) => PatKind::AdtUnit(ctor),
                        }
                    }
                    Err(err) => PatKind::Error(err),
                }
            }
            AstPatKind::PathAndBrace(path, fields, rest) => 'path: {
                let res = match self.resolve_expr_path(path).fail_on_unbound_local() {
                    Ok(v) => v,
                    Err(err) => break 'path PatKind::Error(err),
                };

                let Some(ctor) = res.as_adt_ctor(s).filter(|v| v.def.r(s).syntax.is_named()) else {
                    break 'path PatKind::Error(
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

                let fields = fields
                    .iter()
                    .map(|field| match &field.kind {
                        AstPatFieldKind::WithPat(pat) => {
                            (field.name, self.lower_pat_inner(pat, locals))
                        }
                        AstPatFieldKind::Bare(muta) => {
                            let kind = match locals.resolve(field.name, muta.as_muta(), s) {
                                Ok(name) => PatKind::NewName(name, None),
                                Err(err) => PatKind::Error(err),
                            };

                            (
                                field.name,
                                Obj::new(
                                    Pat {
                                        span: field.name.span,
                                        kind,
                                    },
                                    s,
                                ),
                            )
                        }
                    })
                    .collect::<Vec<_>>();

                let deny_missing = match rest {
                    AstPatStructRest::Rest(_span) => None,
                    AstPatStructRest::None => Some(path.span),
                };

                let fields = Obj::new_iter(
                    self.match_up_ctor_members(ctor.def, fields, deny_missing)
                        .into_iter()
                        .map(|(idx, pat)| PatNamedField { idx, pat }),
                    s,
                );

                PatKind::AdtNamed(ctor, fields)
            }
            AstPatKind::PathAndParen(path, children) => 'pat: {
                let res = match self.resolve_expr_path(path).fail_on_unbound_local() {
                    Ok(v) => v,
                    Err(err) => break 'pat PatKind::Error(err),
                };

                let Some(ctor) = res.as_adt_ctor(s).filter(|v| v.def.r(s).syntax.is_tuple()) else {
                    break 'pat PatKind::Error(
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

                let children = self.lower_pat_list_front_and_tail(children, locals);
                let expected_len = ctor.def.r(s).fields.len() as u32;

                let arity_offense = match children.len(s) {
                    PatListFrontAndTailLen::Exactly(v) if v != expected_len => Some((v, "", "")),
                    PatListFrontAndTailLen::AtLeast(v) if v > expected_len => {
                        Some((v, " at least", "only "))
                    }
                    _ => None,
                };

                if let Some((child_count, at_least, only)) = arity_offense {
                    break 'pat PatKind::Error(
                        Diag::span_err(
                            path.span,
                            format_args!(
                                "this pattern has{at_least} {child_count} field{}, but the \
                                 corresponding tuple {} {only}has {}",
                                if child_count == 1 { "" } else { "s" },
                                res.bare_what(s),
                                expected_len,
                            ),
                        )
                        .emit(),
                    );
                }

                PatKind::AdtTuple(ctor, children)
            }
            AstPatKind::Or(pats) => {
                match locals.fork(|locals| {
                    let mut forks = Vec::new();

                    for pat in pats {
                        forks.push(
                            locals.case(pat.span, |locals| self.lower_pat_inner(pat, locals)),
                        );
                    }

                    Obj::new_slice(&forks, s)
                }) {
                    Ok(forks) => PatKind::Or(forks),
                    Err(err) => PatKind::Error(err),
                }
            }
            AstPatKind::Tuple(pats) => {
                PatKind::Tuple(self.lower_pat_list_front_and_tail(pats, locals))
            }
            AstPatKind::Paren(pat) => return self.lower_pat(pat),
            AstPatKind::Ref(muta, inner) => {
                PatKind::Ref(muta.as_muta(), self.lower_pat_inner(inner, locals))
            }
            AstPatKind::Slice(pats) => {
                PatKind::Slice(self.lower_pat_list_front_and_tail(pats, locals))
            }
            AstPatKind::Rest => PatKind::Error(
                Diag::span_err(ast.span, "`..` patterns are not allowed here")
                    .child(LeafDiag::new(
                        Level::Note,
                        "only allowed in tuple, tuple struct, and slice patterns",
                    ))
                    .emit(),
            ),
            AstPatKind::Range(low, high, limits) => todo!(),
            AstPatKind::Lit(expr) => PatKind::Lit(self.lower_expr(expr)),
            AstPatKind::Error(err) => PatKind::Error(*err),
        };

        Obj::new(
            Pat {
                span: ast.span,
                kind,
            },
            s,
        )
    }

    fn lower_pat_list_inner(
        &mut self,
        asts: &[AstPat],
        locals: &mut PatLocalBranchResolver,
    ) -> Obj<[Obj<Pat>]> {
        let s = &self.tcx.session;

        Obj::new_iter(asts.iter().map(|ast| self.lower_pat_inner(ast, locals)), s)
    }

    pub fn lower_pat_list_front_and_tail_generic<T>(
        &mut self,
        list: impl IntoIterator<Item = T>,
        mut lower: impl FnMut(&mut Self, T) -> PatOrRest,
    ) -> PatListFrontAndTail {
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
                        Diag::anon_err("`..` can only be used once per tuple pattern")
                            .primary(new_span, "can only be used once per tuple pattern")
                            .secondary(prev_span, "previously used here")
                            .emit();
                    } else {
                        found_rest = Some(new_span);
                    }
                }
            }
        }

        PatListFrontAndTail {
            front: Obj::new_slice(&front, s),
            tail: found_rest.map(|_| Obj::new_slice(&tail, s)),
        }
    }

    pub fn lower_pat_list_front_and_tail(
        &mut self,
        asts: &[AstPat],
        locals: &mut PatLocalBranchResolver,
    ) -> PatListFrontAndTail {
        self.lower_pat_list_front_and_tail_generic(asts, |this, ast| match &ast.kind {
            AstPatKind::Rest => PatOrRest::Rest(ast.span),
            _ => PatOrRest::Pat(this.lower_pat_inner(ast, locals)),
        })
    }
}

#[derive(Debug, Copy, Clone)]
pub enum PatOrRest {
    Pat(Obj<Pat>),
    Rest(Span),
}
