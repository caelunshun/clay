use crate::{
    base::{
        Diag, ErrorGuaranteed, LeafDiag,
        syntax::{Span, Symbol},
    },
    kw,
    parse::token::Ident,
    utils::{hash::FxHashSet, mem::Handle},
};
use std::fmt;

// === Generic === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum AnyDef<M, I> {
    Module(M),
    Item(I),
}

impl<M, I> AnyDef<M, I> {
    pub fn as_module(self) -> Option<M> {
        match self {
            AnyDef::Module(v) => Some(v),
            AnyDef::Item(_) => None,
        }
    }

    pub fn as_item(self) -> Option<I> {
        match self {
            AnyDef::Item(v) => Some(v),
            AnyDef::Module(_) => None,
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum StepLookupError {
    NotFound,
    NotVisible,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum EmitErrors {
    Yes,
    No,
}

#[derive(Debug, Copy, Clone)]
pub enum ParentKind<M> {
    Real(Option<M>),
    Scoped(M),
}

impl<M> ParentKind<M> {
    pub fn as_option(self) -> Option<M> {
        match self {
            ParentKind::Real(v) => v,
            ParentKind::Scoped(v) => Some(v),
        }
    }

    pub fn map<N>(self, f: impl FnOnce(M) -> N) -> ParentKind<N> {
        match self {
            ParentKind::Real(v) => ParentKind::Real(v.map(f)),
            ParentKind::Scoped(v) => ParentKind::Scoped(f(v)),
        }
    }
}

pub trait ParentResolver {
    type Module: Handle;

    fn direct_parent(&self, def: Self::Module) -> ParentKind<Self::Module>;

    fn module_root(&self, def: Self::Module) -> Self::Module {
        let mut curr = def;

        loop {
            match self.direct_parent(curr) {
                ParentKind::Scoped(next) => {
                    curr = next;
                }
                ParentKind::Real(_) => return curr,
            }
        }
    }

    fn module_parent(&self, def: Self::Module) -> Option<Self::Module> {
        let mut curr = self.direct_parent(def);

        loop {
            match curr {
                ParentKind::Scoped(next) => {
                    curr = self.direct_parent(next);
                }
                ParentKind::Real(out) => break out,
            }
        }
    }

    fn is_descendant(&self, mut descendant: Self::Module, ancestor: Self::Module) -> bool {
        loop {
            if descendant == ancestor {
                return true;
            }

            let Some(parent) = self.module_parent(descendant) else {
                return false;
            };

            descendant = parent;
        }
    }
}

pub trait ModuleResolver: ParentResolver {
    type Item: Handle;

    fn path(&self, def: AnyDef<Self::Module, Self::Item>) -> impl 'static + Copy + fmt::Display;

    fn global_use_count(&mut self, curr: Self::Module) -> u32;

    fn global_use_span(&mut self, curr: Self::Module, use_idx: u32) -> Span;

    fn global_use_target(
        &mut self,
        vis_ctxt: Self::Module,
        curr: Self::Module,
        use_idx: u32,
    ) -> Result<Self::Module, StepLookupError>;

    fn lookup_direct(
        &mut self,
        vis_ctxt: Self::Module,
        curr: Self::Module,
        name: Symbol,
    ) -> Result<AnyDef<Self::Module, Self::Item>, StepLookupError>;

    fn lookup(
        &mut self,
        module_root: Self::Module,
        vis_ctxt: Self::Module,
        origin: Self::Module,
        path: &[Ident],
        emit_errors: EmitErrors,
    ) -> Result<AnyDef<Self::Module, Self::Item>, Option<ErrorGuaranteed>> {
        lookup_inner(
            self,
            module_root,
            vis_ctxt,
            origin,
            path,
            emit_errors,
            &mut FxHashSet::default(),
        )
    }
}

fn lookup_inner<R>(
    resolver: &mut R,
    module_root: R::Module,
    vis_ctxt: R::Module,
    origin: R::Module,
    path: &[Ident],
    emit_errors: EmitErrors,
    reentrant_glob_lookups: &mut FxHashSet<R::Module>,
) -> Result<AnyDef<R::Module, R::Item>, Option<ErrorGuaranteed>>
where
    R: ?Sized + ModuleResolver,
{
    let mut finger = AnyDef::Module(origin);

    let mut parts_iter = path.iter();

    fn make_err<M, I>(
        emit_errors: EmitErrors,
        f: impl FnOnce() -> Diag<ErrorGuaranteed>,
    ) -> Result<AnyDef<M, I>, Option<ErrorGuaranteed>> {
        match emit_errors {
            EmitErrors::Yes => Err(Some(f().emit())),
            EmitErrors::No => Err(None),
        }
    }

    'traverse: while let (Some(part), &AnyDef::Module(curr_scope_start)) =
        (parts_iter.next(), &finger)
    {
        // Handle special path parts.
        if part.matches_kw(kw!("self")) {
            finger = AnyDef::Module(resolver.module_root(curr_scope_start));
            continue 'traverse;
        }

        if part.matches_kw(kw!("crate")) {
            finger = AnyDef::Module(module_root);
            continue 'traverse;
        }

        if part.matches_kw(kw!("super")) {
            let Some(parent) = resolver.module_parent(curr_scope_start) else {
                return make_err(emit_errors, || {
                    Diag::span_err(part.span, "`super` cannot apply to crate root")
                });
            };

            finger = AnyDef::Module(parent);
            continue 'traverse;
        }

        let mut curr_scope_curr = curr_scope_start;

        loop {
            // Attempt to resolve a direct link.
            match resolver.lookup_direct(vis_ctxt, curr_scope_curr, part.text) {
                Ok(link) => {
                    finger = link;
                    continue 'traverse;
                }
                Err(StepLookupError::NotVisible) => {
                    return make_err(emit_errors, || {
                        Diag::span_err(part.span, "item is not visible to the current module")
                    });
                }
                Err(StepLookupError::NotFound) => {
                    // (fallthrough)
                }
            }

            // Otherwise, attempt to follow a global import.
            'glob_import: {
                // Ensure that we're not reentrantly trying to glob-import from the same module.
                if !reentrant_glob_lookups.insert(curr_scope_curr) {
                    break 'glob_import;
                }

                // Collect resolutions
                let mut resolutions = Vec::new();

                for use_idx in 0..resolver.global_use_count(curr_scope_curr) {
                    let target =
                        match resolver.global_use_target(vis_ctxt, curr_scope_curr, use_idx) {
                            Ok(target) => target,
                            Err(StepLookupError::NotFound) | Err(StepLookupError::NotVisible) => {
                                continue;
                            }
                        };

                    let resolution = lookup_inner(
                        resolver,
                        module_root,
                        vis_ctxt,
                        target,
                        &[*part],
                        EmitErrors::No,
                        reentrant_glob_lookups,
                    );

                    let Ok(resolution) = resolution else {
                        continue;
                    };

                    resolutions.push((
                        resolution,
                        resolver.global_use_span(curr_scope_curr, use_idx),
                    ));
                }

                reentrant_glob_lookups.remove(&curr_scope_curr);

                // Ensure that our resolution is unambiguous.
                let Some(((first, first_span), remainder)) = resolutions.split_first() else {
                    break 'glob_import;
                };

                for (other, other_span) in remainder {
                    if first != other {
                        return make_err(emit_errors, || {
                            Diag::span_err(
                                part.span,
                                format_args!("resolutions for `{}` are ambiguous", part.text),
                            )
                            .child(LeafDiag::span_note(
                                *first_span,
                                format_args!(
                                    "first glob import resolves to `{}`",
                                    resolver.path(*first),
                                ),
                            ))
                            .child(LeafDiag::span_note(
                                *other_span,
                                format_args!(
                                    "second glob import resolves to `{}`",
                                    resolver.path(*other),
                                ),
                            ))
                        });
                    }
                }

                finger = resolutions.into_iter().next().unwrap().0;
                continue 'traverse;
            }

            curr_scope_curr = match resolver.direct_parent(curr_scope_curr) {
                ParentKind::Scoped(next) => next,
                ParentKind::Real(_) => break,
            };
        }

        // Nothing could provide this path part!
        return make_err(emit_errors, || {
            Diag::span_err(
                part.span,
                format_args!(
                    "`{}` not found in `{}`",
                    part.text,
                    resolver.path(AnyDef::Module(curr_scope_start))
                ),
            )
        });
    }

    match finger {
        AnyDef::Module(module) => {
            debug_assert_eq!(resolver.module_root(module), module);
            Ok(AnyDef::Module(module))
        }
        AnyDef::Item(item) => {
            if parts_iter.len() == 0 {
                Ok(AnyDef::Item(item))
            } else {
                make_err(emit_errors, || {
                    Diag::span_err(path[path.len() - parts_iter.len() - 1].span, "not a module")
                })
            }
        }
    }
}
