use crate::{
    base::{
        Diag, ErrorGuaranteed, LeafDiag, Session,
        syntax::{HasSpan as _, Span, Symbol},
    },
    parse::ast::{AstBarePath, AstPathPart, AstPathPartKind, AstPathPartKw},
    symbol,
    utils::{hash::FxHashSet, mem::Handle},
};
use std::fmt;

// === ItemCategory === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum ItemCategoryUse {
    VisibilityTarget,
    GlobUseTarget,
}

impl ItemCategoryUse {
    pub fn as_a_what(self) -> Symbol {
        match self {
            ItemCategoryUse::VisibilityTarget => symbol!("visibility target"),
            ItemCategoryUse::GlobUseTarget => symbol!("glob-use target"),
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum ItemCategory {
    Module,
    Scope,
    Impl,
    Trait,
    Struct,
    Enum,
    EnumVariant,
    Func,
}

impl ItemCategory {
    pub fn bare_what(self) -> Symbol {
        match self {
            ItemCategory::Module | ItemCategory::Scope => symbol!("module"),
            ItemCategory::Impl => symbol!("impl"),
            ItemCategory::Trait => symbol!("trait"),
            ItemCategory::Struct => symbol!("struct"),
            ItemCategory::Enum => symbol!("enum"),
            ItemCategory::EnumVariant => symbol!("enum variant"),
            ItemCategory::Func => symbol!("function"),
        }
    }

    pub fn a_what(self) -> Symbol {
        match self {
            ItemCategory::Module | ItemCategory::Scope => symbol!("a module"),
            ItemCategory::Impl => symbol!("an impl"),
            ItemCategory::Trait => symbol!("a trait"),
            ItemCategory::Struct => symbol!("a struct"),
            ItemCategory::Enum => symbol!("an enum"),
            ItemCategory::EnumVariant => symbol!("an enum variant"),
            ItemCategory::Func => symbol!("a function"),
        }
    }

    pub fn is_valid_for_use(self, for_use: ItemCategoryUse) -> bool {
        match for_use {
            ItemCategoryUse::VisibilityTarget => match self {
                ItemCategory::Module | ItemCategory::Scope => true,
                ItemCategory::Impl
                | ItemCategory::Trait
                | ItemCategory::Struct
                | ItemCategory::Enum
                | ItemCategory::EnumVariant
                | ItemCategory::Func => false,
            },
            ItemCategoryUse::GlobUseTarget => match self {
                ItemCategory::Module | ItemCategory::Scope | ItemCategory::Enum => true,
                ItemCategory::Impl
                | ItemCategory::Trait
                | ItemCategory::Struct
                | ItemCategory::EnumVariant
                | ItemCategory::Func => false,
            },
        }
    }

    pub fn is_valid_for_super(self) -> bool {
        match self {
            ItemCategory::Module => true,
            ItemCategory::Scope
            | ItemCategory::Impl
            | ItemCategory::Trait
            | ItemCategory::Struct
            | ItemCategory::Enum
            | ItemCategory::EnumVariant
            | ItemCategory::Func => false,
        }
    }
}

// === Resolver === //

#[derive(Debug, Copy, Clone)]
pub enum ParentRef<T> {
    Real(Option<T>),
    Scoped(T),
}

impl<T> ParentRef<T> {
    pub fn as_option(self) -> Option<T> {
        match self {
            ParentRef::Real(v) => v,
            ParentRef::Scoped(v) => Some(v),
        }
    }

    pub fn unwrap(self) -> T {
        self.as_option().unwrap()
    }

    pub fn map<V>(self, f: impl FnOnce(T) -> V) -> ParentRef<V> {
        match self {
            ParentRef::Real(v) => ParentRef::Real(v.map(f)),
            ParentRef::Scoped(v) => ParentRef::Scoped(f(v)),
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum StepLookupError {
    NotFound,
    NotVisible,
}

#[derive(Debug, Clone)]
pub enum StepResolveError<T> {
    CannotSuperInRoot,
    CannotSuperOnNonModule,
    DeniedVisibility,
    Ambiguous([(T, Span); 2]),
    NotFound,
}

impl<T: Handle> StepResolveError<T> {
    pub fn emit(
        self,
        resolver: &(impl ?Sized + PathResolver<Item = T>),
        curr: T,
        part: AstPathPart,
    ) -> ErrorGuaranteed {
        match self {
            StepResolveError::CannotSuperInRoot => {
                Diag::span_err(part.span(), "`super` cannot apply to crate root").emit()
            }
            StepResolveError::CannotSuperOnNonModule => Diag::span_err(
                part.span(),
                format_args!(
                    "`super` can only be applied to a module, not {}",
                    resolver.categorize(curr).a_what()
                ),
            )
            .emit(),
            StepResolveError::DeniedVisibility => {
                Diag::span_err(part.span(), "item is not visible to the current module").emit()
            }
            StepResolveError::Ambiguous(conflicts) => {
                let [(first, first_span), (other, other_span)] = conflicts;

                Diag::span_err(
                    part.span(),
                    format_args!("resolutions for `{}` are ambiguous", part.raw().text),
                )
                .child(LeafDiag::span_note(
                    first_span,
                    format_args!("first glob import resolves to `{}`", resolver.path(first)),
                ))
                .child(LeafDiag::span_note(
                    other_span,
                    format_args!("second glob import resolves to `{}`", resolver.path(other)),
                ))
                .emit()
            }
            StepResolveError::NotFound => Diag::span_err(
                part.span(),
                format_args!(
                    "`{}` not found in `{}`",
                    part.raw().text,
                    resolver.path(curr),
                ),
            )
            .emit(),
        }
    }
}

#[derive(Copy, Clone)]
pub struct ItemPathFmt {
    pub prefix: Symbol,
    pub main_part: Symbol,
}

impl fmt::Display for ItemPathFmt {
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

pub trait ParentResolver {
    type Item: Handle;

    fn categorize(&self, def: Self::Item) -> ItemCategory;

    fn direct_parent(&self, def: Self::Item) -> ParentRef<Self::Item>;

    fn scope_root(&self, def: Self::Item) -> Self::Item {
        let mut curr = def;

        loop {
            match self.direct_parent(curr) {
                ParentRef::Scoped(next) => {
                    curr = next;
                }
                ParentRef::Real(_) => return curr,
            }
        }
    }

    fn parent_module(&self, def: Self::Item) -> Option<Self::Item> {
        let mut curr = self.direct_parent(def);

        loop {
            match curr {
                ParentRef::Scoped(next) => {
                    curr = self.direct_parent(next);
                }
                ParentRef::Real(out) => break out,
            }
        }
    }

    fn is_descendant(&self, mut descendant: Self::Item, ancestor: Self::Item) -> bool {
        descendant = self.scope_root(descendant);

        loop {
            if descendant == ancestor {
                return true;
            }

            let Some(parent) = self.parent_module(descendant) else {
                return false;
            };

            descendant = parent;
        }
    }
}

pub trait PathResolver: ParentResolver {
    fn path(&self, def: Self::Item) -> ItemPathFmt;

    fn global_use_count(&mut self, curr: Self::Item) -> u32;

    fn global_use_span(&mut self, curr: Self::Item, use_idx: u32) -> Span;

    fn global_use_target(
        &mut self,
        vis_ctxt: Self::Item,
        curr: Self::Item,
        use_idx: u32,
    ) -> Result<Self::Item, StepLookupError>;

    fn lookup_direct(
        &mut self,
        vis_ctxt: Self::Item,
        curr: Self::Item,
        name: Symbol,
    ) -> Result<Self::Item, StepLookupError>;

    fn resolve_step(
        &mut self,
        local_crate_root: Self::Item,
        vis_ctxt: Self::Item,
        finger: Self::Item,
        part: AstPathPart,
    ) -> Result<Self::Item, StepResolveError<Self::Item>> {
        resolve_step_inner(
            self,
            local_crate_root,
            vis_ctxt,
            finger,
            part,
            &mut FxHashSet::default(),
        )
    }

    fn resolve_bare_path(
        &mut self,
        local_crate_root: Self::Item,
        origin: Self::Item,
        path: &AstBarePath,
    ) -> Result<Self::Item, ErrorGuaranteed> {
        let mut finger = origin;

        for &part in path.parts.iter() {
            match self.resolve_step(local_crate_root, origin, finger, part) {
                Ok(next) => finger = next,
                Err(err) => return Err(err.emit(self, finger, part)),
            }
        }

        Ok(finger)
    }

    fn resolve_bare_path_for_use(
        &mut self,
        local_crate_root: Self::Item,
        origin: Self::Item,
        path: &AstBarePath,
        for_use: Option<ItemCategoryUse>,
    ) -> Result<Self::Item, ErrorGuaranteed> {
        let target = self.resolve_bare_path(local_crate_root, origin, path)?;
        let category = self.categorize(target);

        if let Some(for_use) = for_use
            && !category.is_valid_for_use(for_use)
        {
            return Err(Diag::span_err(
                path.span,
                format_args!(
                    "{} cannot be used as {}",
                    category.bare_what(),
                    for_use.as_a_what()
                ),
            )
            .emit());
        }

        Ok(target)
    }
}

pub trait VisibilityResolver: PathResolver {
    fn resolve_visibility_target(
        &mut self,
        local_crate_root: Self::Item,
        origin: Self::Item,
        path: &AstBarePath,
    ) -> Result<Self::Item, ErrorGuaranteed> {
        let target = self.resolve_bare_path_for_use(
            local_crate_root,
            origin,
            path,
            Some(ItemCategoryUse::VisibilityTarget),
        )?;

        if !self.is_descendant(origin, target) {
            return Err(Diag::span_err(
                path.span,
                format_args!(
                    "`{}` is not an ancestor of the current module (`{}`)",
                    self.path(target),
                    self.path(self.scope_root(origin)),
                ),
            )
            .emit());
        }

        Ok(target)
    }
}

fn resolve_step_inner<R>(
    resolver: &mut R,
    local_crate_root: R::Item,
    vis_ctxt: R::Item,
    finger: R::Item,
    part: AstPathPart,
    reentrant_glob_lookups: &mut FxHashSet<R::Item>,
) -> Result<R::Item, StepResolveError<R::Item>>
where
    R: ?Sized + PathResolver,
{
    // Handle special path parts.
    let part = match part.kind() {
        AstPathPartKind::Keyword(_, AstPathPartKw::Self_) => {
            return Ok(resolver.scope_root(finger));
        }
        AstPathPartKind::Keyword(_, AstPathPartKw::Crate) => {
            return Ok(local_crate_root);
        }
        AstPathPartKind::Keyword(_, AstPathPartKw::Super) => {
            if !resolver.categorize(finger).is_valid_for_super() {
                return Err(StepResolveError::CannotSuperOnNonModule);
            }

            let Some(parent) = resolver.parent_module(finger) else {
                return Err(StepResolveError::CannotSuperInRoot);
            };

            return Ok(parent);
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
            let mut first_resolution = None::<(R::Item, Span)>;

            for use_idx in 0..resolver.global_use_count(scope_finger) {
                let target = match resolver.global_use_target(vis_ctxt, scope_finger, use_idx) {
                    Ok(target) => target,
                    Err(StepLookupError::NotFound) | Err(StepLookupError::NotVisible) => {
                        continue;
                    }
                };

                let resolution = resolve_step_inner(
                    resolver,
                    local_crate_root,
                    vis_ctxt,
                    target,
                    AstPathPart::new_ident(part),
                    reentrant_glob_lookups,
                );

                let resolution = match resolution {
                    Ok(v) => v,
                    Err(
                        StepResolveError::CannotSuperInRoot
                        | StepResolveError::CannotSuperOnNonModule,
                    ) => {
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
            ParentRef::Scoped(next) => next,
            ParentRef::Real(_) => break,
        };
    }

    // Nothing could provide this path part!
    Err(StepResolveError::NotFound)
}
