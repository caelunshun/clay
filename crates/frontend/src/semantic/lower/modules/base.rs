use crate::{
    base::{
        Diag, ErrorGuaranteed, LeafDiag, Session,
        syntax::{HasSpan as _, Span, Symbol},
    },
    parse::ast::{AstPathPart, AstPathPartKind, AstPathPartKw},
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

pub type StepResolveResult<R> = Result<
    AnyDef<<R as ParentResolver>::Module, <R as ModuleResolver>::Item>,
    StepResolveError<<R as ParentResolver>::Module, <R as ModuleResolver>::Item>,
>;

#[derive(Debug, Clone)]
pub enum StepResolveError<M, I> {
    CannotSuperInRoot,
    DeniedVisibility,
    Ambiguous([(AnyDef<M, I>, Span); 2]),
    NotFound,
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

    fn resolve_noisy(
        &mut self,
        module_root: Self::Module,
        origin: Self::Module,
        path: &[AstPathPart],
    ) -> Result<AnyDef<Self::Module, Self::Item>, ErrorGuaranteed> {
        self.resolve(module_root, origin, origin, path, EmitErrors::Yes)
            .map_err(Option::unwrap)
    }

    fn resolve_silent(
        &mut self,
        module_root: Self::Module,
        origin: Self::Module,
        path: &[AstPathPart],
    ) -> Option<AnyDef<Self::Module, Self::Item>> {
        self.resolve(module_root, origin, origin, path, EmitErrors::No)
            .ok()
    }

    fn resolve(
        &mut self,
        module_root: Self::Module,
        vis_ctxt: Self::Module,
        origin: Self::Module,
        path: &[AstPathPart],
        emit_errors: EmitErrors,
    ) -> Result<AnyDef<Self::Module, Self::Item>, Option<ErrorGuaranteed>> {
        let mut finger = AnyDef::Module(origin);
        let mut parts_iter = path.iter();

        #[track_caller]
        fn make_err<M, I>(
            emit_errors: EmitErrors,
            f: impl FnOnce() -> Diag<ErrorGuaranteed>,
        ) -> Result<AnyDef<M, I>, Option<ErrorGuaranteed>> {
            match emit_errors {
                EmitErrors::Yes => Err(Some(f().emit())),
                EmitErrors::No => Err(None),
            }
        }

        while let &AnyDef::Module(curr) = &finger {
            // N.B. We have to ensure that the `finger` is on a module before consuming the next part.
            let Some(&part) = parts_iter.next() else {
                break;
            };

            match self.resolve_step(module_root, vis_ctxt, curr, part) {
                Ok(next) => finger = next,
                Err(StepResolveError::CannotSuperInRoot) => {
                    return make_err(emit_errors, || {
                        Diag::span_err(part.span(), "`super` cannot apply to crate root")
                    });
                }
                Err(StepResolveError::DeniedVisibility) => {
                    return make_err(emit_errors, || {
                        Diag::span_err(part.span(), "item is not visible to the current module")
                    });
                }
                Err(StepResolveError::Ambiguous(conflicts)) => {
                    let [(first, first_span), (other, other_span)] = conflicts;

                    return make_err(emit_errors, || {
                        Diag::span_err(
                            part.span(),
                            format_args!("resolutions for `{}` are ambiguous", part.raw().text),
                        )
                        .child(LeafDiag::span_note(
                            first_span,
                            format_args!("first glob import resolves to `{}`", self.path(first)),
                        ))
                        .child(LeafDiag::span_note(
                            other_span,
                            format_args!("second glob import resolves to `{}`", self.path(other)),
                        ))
                    });
                }
                Err(StepResolveError::NotFound) => {
                    return make_err(emit_errors, || {
                        Diag::span_err(
                            part.span(),
                            format_args!(
                                "`{}` not found in `{}`",
                                part.raw().text,
                                self.path(AnyDef::Module(curr))
                            ),
                        )
                    });
                }
            }
        }

        match finger {
            AnyDef::Module(module) => {
                debug_assert_eq!(self.module_root(module), module);
                Ok(AnyDef::Module(module))
            }
            AnyDef::Item(item) => {
                if parts_iter.len() == 0 {
                    Ok(AnyDef::Item(item))
                } else {
                    make_err(emit_errors, || {
                        Diag::span_err(
                            path[path.len() - parts_iter.len() - 1].span(),
                            "not a module",
                        )
                    })
                }
            }
        }
    }

    fn resolve_step(
        &mut self,
        module_root: Self::Module,
        vis_ctxt: Self::Module,
        finger: Self::Module,
        part: AstPathPart,
    ) -> StepResolveResult<Self> {
        resolve_step_inner(
            self,
            module_root,
            vis_ctxt,
            finger,
            part,
            &mut FxHashSet::default(),
        )
    }
}

fn resolve_step_inner<R>(
    resolver: &mut R,
    module_root: R::Module,
    vis_ctxt: R::Module,
    finger: R::Module,
    part: AstPathPart,
    reentrant_glob_lookups: &mut FxHashSet<R::Module>,
) -> StepResolveResult<R>
where
    R: ?Sized + ModuleResolver,
{
    // Handle special path parts.
    let part = match part.kind() {
        AstPathPartKind::Keyword(_, AstPathPartKw::Self_) => {
            return Ok(AnyDef::Module(resolver.module_root(finger)));
        }
        AstPathPartKind::Keyword(_, AstPathPartKw::Crate) => {
            return Ok(AnyDef::Module(module_root));
        }
        AstPathPartKind::Keyword(_, AstPathPartKw::Super) => {
            let Some(parent) = resolver.module_parent(finger) else {
                return Err(StepResolveError::CannotSuperInRoot);
            };

            return Ok(AnyDef::Module(parent));
        }
        AstPathPartKind::Regular(ident) => ident,
    };

    let mut scope_finger = finger;

    // Otherwise, walk the scopes and attempt to find a suitable link.
    loop {
        // Attempt to resolve a direct link.
        match resolver.lookup_direct(vis_ctxt, scope_finger, part.text) {
            Ok(link) => {
                return Ok(link);
            }
            Err(StepLookupError::NotVisible) => {
                return Err(StepResolveError::DeniedVisibility);
            }
            Err(StepLookupError::NotFound) => {
                // (fallthrough)
            }
        }

        // Otherwise, attempt to follow a global import.
        'glob_import: {
            // Ensure that we're not reentrantly trying to glob-import from the same module.
            if !reentrant_glob_lookups.insert(scope_finger) {
                break 'glob_import;
            }

            // Collect resolutions
            let mut first_resolution = None::<(AnyDef<R::Module, R::Item>, Span)>;

            for use_idx in 0..resolver.global_use_count(scope_finger) {
                let target = match resolver.global_use_target(vis_ctxt, scope_finger, use_idx) {
                    Ok(target) => target,
                    Err(StepLookupError::NotFound) | Err(StepLookupError::NotVisible) => {
                        continue;
                    }
                };

                let resolution = resolve_step_inner(
                    resolver,
                    module_root,
                    vis_ctxt,
                    target,
                    AstPathPart::new_ident(part),
                    reentrant_glob_lookups,
                );

                let resolution = match resolution {
                    Ok(v) => v,
                    Err(StepResolveError::CannotSuperInRoot) => {
                        unreachable!()
                    }
                    Err(StepResolveError::Ambiguous(other_resolutions)) => {
                        return Err(StepResolveError::Ambiguous(other_resolutions));
                    }
                    Err(StepResolveError::DeniedVisibility | StepResolveError::NotFound) => {
                        continue;
                    }
                };

                let resolution_span = resolver.global_use_span(scope_finger, use_idx);

                if let Some((first_resolution, first_resolution_span)) = first_resolution {
                    if resolution != first_resolution {
                        return Err(StepResolveError::Ambiguous([
                            (first_resolution, first_resolution_span),
                            (resolution, resolution_span),
                        ]));
                    }
                } else {
                    first_resolution = Some((resolution, resolution_span));
                }
            }

            reentrant_glob_lookups.remove(&scope_finger);

            // Ensure that our resolution is unambiguous.
            let Some((first, _first_span)) = first_resolution else {
                break 'glob_import;
            };

            return Ok(first);
        }

        scope_finger = match resolver.direct_parent(scope_finger) {
            ParentKind::Scoped(next) => next,
            ParentKind::Real(_) => break,
        };
    }

    // Nothing could provide this path part!
    Err(StepResolveError::NotFound)
}

// === Helpers === //

#[derive(Copy, Clone)]
pub struct ModulePathFmt {
    pub prefix: Symbol,
    pub main_part: Symbol,
}

impl fmt::Display for ModulePathFmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = &Session::fetch();

        f.write_str(self.prefix.as_str(s))?;

        let main_part = self.main_part.as_str(s);
        if !main_part.is_empty() {
            f.write_str("::")?;
            f.write_str(main_part)?;
        }

        Ok(())
    }
}
