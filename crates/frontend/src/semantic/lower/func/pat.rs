use crate::{
    base::{
        Diag, ErrorGuaranteed, LeafDiag, Session,
        arena::Obj,
        syntax::{Span, Symbol},
    },
    parse::{
        ast::{AstPat, AstPatKind},
        token::Ident,
    },
    semantic::{
        lower::{
            entry::IntraItemLowerCtxt,
            func::path::{ExprPathIdentOrResolution, PathResolvedPattern},
        },
        syntax::{FuncLocal, Mutability, Pat, PatKind},
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
                // TODO: Lower the remainder

                let res = self.resolve_expr_path(path);

                match res.as_ident_or_res(path, s) {
                    Ok(ExprPathIdentOrResolution::Ident(name)) => {
                        match locals.resolve(name, binding_mode.local_muta.as_muta(), s) {
                            Ok(local) => {
                                self.func_local_names.define_force_shadow(name.text, local);

                                PatKind::NewName(local)
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

                        match kind {
                            PathResolvedPattern::UnitCtor(ctor) => PatKind::AdtUnit(ctor),
                        }
                    }
                    Err(err) => PatKind::Error(err),
                }
            }
            AstPatKind::PathAndBrace(ast_expr_path, ast_pat_fields, ast_pat_struct_rest) => todo!(),
            AstPatKind::PathAndParen(ast_expr_path, ast_pats) => todo!(),
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
            AstPatKind::Tuple(pats) => PatKind::Tuple(self.lower_pat_list_inner(pats, locals)),
            AstPatKind::Paren(pat) => return self.lower_pat(pat),
            AstPatKind::Ref(ast_opt_mutability, ast_pat) => todo!(),
            AstPatKind::Slice(pats) => PatKind::Slice(self.lower_pat_list_inner(pats, locals)),
            AstPatKind::Rest => todo!(),
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
}
