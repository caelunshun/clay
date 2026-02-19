use crate::{
    base::{
        Diag, ErrorGuaranteed, LeafDiag, Session,
        syntax::{HasSpan as _, Span, Symbol},
    },
    parse::ast::{AstBarePath, AstPathPart, AstPathPartKind, AstPathPartKw},
    symbol,
    utils::{hash::FxHashSet, mem::Handle},
};
use smallvec::SmallVec;
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
    Impl,
    Trait,
    Struct,
    Enum,
    EnumVariant,
    Fn,
    TypeAlias,
}

impl ItemCategory {
    pub fn bare_what(self) -> Symbol {
        match self {
            ItemCategory::Module => symbol!("module"),
            ItemCategory::Impl => symbol!("impl"),
            ItemCategory::Trait => symbol!("trait"),
            ItemCategory::Struct => symbol!("struct"),
            ItemCategory::Enum => symbol!("enum"),
            ItemCategory::EnumVariant => symbol!("enum variant"),
            ItemCategory::Fn => symbol!("function"),
            ItemCategory::TypeAlias => symbol!("type"),
        }
    }

    pub fn a_what(self) -> Symbol {
        match self {
            ItemCategory::Module => symbol!("a module"),
            ItemCategory::Impl => symbol!("an impl"),
            ItemCategory::Trait => symbol!("a trait"),
            ItemCategory::Struct => symbol!("a struct"),
            ItemCategory::Enum => symbol!("an enum"),
            ItemCategory::EnumVariant => symbol!("an enum variant"),
            ItemCategory::Fn => symbol!("a function"),
            ItemCategory::TypeAlias => symbol!("a type"),
        }
    }

    pub fn is_valid_for_use(self, for_use: ItemCategoryUse) -> bool {
        match for_use {
            ItemCategoryUse::VisibilityTarget => match self {
                ItemCategory::Module => true,
                ItemCategory::Impl
                | ItemCategory::Trait
                | ItemCategory::Struct
                | ItemCategory::Enum
                | ItemCategory::EnumVariant
                | ItemCategory::Fn
                | ItemCategory::TypeAlias => false,
            },
            ItemCategoryUse::GlobUseTarget => match self {
                ItemCategory::Module | ItemCategory::Enum => true,
                ItemCategory::Impl
                | ItemCategory::Trait
                | ItemCategory::Struct
                | ItemCategory::EnumVariant
                | ItemCategory::Fn
                | ItemCategory::TypeAlias => false,
            },
        }
    }

    pub fn is_valid_for_special(self) -> bool {
        match self {
            ItemCategory::Module => true,
            ItemCategory::Impl
            | ItemCategory::Trait
            | ItemCategory::Struct
            | ItemCategory::Enum
            | ItemCategory::EnumVariant
            | ItemCategory::Fn
            | ItemCategory::TypeAlias => false,
        }
    }

    pub fn looks_up_parent(self) -> bool {
        match self {
            ItemCategory::Module => false,
            ItemCategory::Impl
            | ItemCategory::Trait
            | ItemCategory::Struct
            | ItemCategory::Enum
            | ItemCategory::EnumVariant
            | ItemCategory::Fn
            | ItemCategory::TypeAlias => true,
        }
    }
}

// === Resolver === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum StepLookupError {
    NotFound,
    NotVisible,
}

#[derive(Debug, Clone)]
pub enum StepResolveError<T> {
    CannotSuperInRoot,
    CannotKeywordOnNonModule(AstPathPartKw),
    DeniedVisibility,
    Ambiguous([(T, Span); 2]),
    NotFound,
}

impl<T: Handle> StepResolveError<T> {
    #[must_use]
    pub fn bind(self, curr: T, part: AstPathPart) -> PathResolveError<T> {
        PathResolveError {
            error: self,
            curr,
            part,
        }
    }

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
            StepResolveError::CannotKeywordOnNonModule(kw) => Diag::span_err(
                part.span(),
                format_args!(
                    "`{}` can only be applied to a module, not {}",
                    kw.kw().str(),
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

#[derive(Debug, Clone)]
pub struct PathResolveError<T: Handle> {
    pub error: StepResolveError<T>,
    pub curr: T,
    pub part: AstPathPart,
}

impl<T: Handle> PathResolveError<T> {
    pub fn emit(self, resolver: &(impl ?Sized + PathResolver<Item = T>)) -> ErrorGuaranteed {
        self.error.emit(resolver, self.curr, self.part)
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

    fn direct_parent(&self, def: Self::Item) -> Option<Self::Item>;

    fn scope_prelude(&self, def: Self::Item) -> Option<Self::Item>;

    fn is_descendant(&self, mut descendant: Self::Item, ancestor: Self::Item) -> bool {
        loop {
            if descendant == ancestor {
                return true;
            }

            let Some(parent) = self.direct_parent(descendant) else {
                return false;
            };

            descendant = parent;
        }
    }

    fn module_root(&self, mut def: Self::Item) -> Self::Item {
        loop {
            if !self.categorize(def).looks_up_parent() {
                break;
            }

            let Some(parent) = self.direct_parent(def) else {
                break;
            };

            def = parent;
        }

        def
    }

    fn module_parent(&self, def: Self::Item) -> Option<Self::Item> {
        let def = self.module_root(def);
        self.direct_parent(def)
    }

    fn scope_components(&self, mut def: Self::Item) -> SmallVec<[Self::Item; 3]> {
        let mut collector = SmallVec::new();

        loop {
            collector.push(def);

            if !self.categorize(def).looks_up_parent() {
                break;
            }

            let Some(parent) = self.direct_parent(def) else {
                break;
            };

            def = parent;
        }

        if let Some(prelude) = self.scope_prelude(def) {
            collector.push(prelude);
        }

        collector
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
        // If we're in the visibility root, allow the first component to be
        if vis_ctxt == finger {
            for finger in self.scope_components(finger) {
                match resolve_step_inner(
                    self,
                    local_crate_root,
                    vis_ctxt,
                    finger,
                    part,
                    &mut FxHashSet::default(),
                ) {
                    Err(StepResolveError::NotFound) => {}
                    res @ (Ok(_) | Err(_)) => return res,
                }
            }

            return Err(StepResolveError::NotFound);
        }

        resolve_step_inner(
            self,
            local_crate_root,
            vis_ctxt,
            finger,
            part,
            &mut FxHashSet::default(),
        )
    }

    fn try_resolve_bare_path(
        &mut self,
        local_crate_root: Self::Item,
        origin: Self::Item,
        path: &AstBarePath,
    ) -> Result<Self::Item, PathResolveError<Self::Item>> {
        let mut finger = origin;

        for &part in path.parts.iter() {
            match self.resolve_step(local_crate_root, origin, finger, part) {
                Ok(next) => finger = next,
                Err(err) => return Err(err.bind(finger, part)),
            }
        }

        Ok(finger)
    }

    fn resolve_bare_path(
        &mut self,
        local_crate_root: Self::Item,
        origin: Self::Item,
        path: &AstBarePath,
    ) -> Result<Self::Item, ErrorGuaranteed> {
        self.try_resolve_bare_path(local_crate_root, origin, path)
            .map_err(|err| err.emit(self))
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
                    self.path(origin),
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
        AstPathPartKind::Keyword(_, kw) => {
            if !resolver.categorize(finger).is_valid_for_special() {
                return Err(StepResolveError::CannotKeywordOnNonModule(kw));
            }

            match kw {
                AstPathPartKw::Self_ => {
                    return Ok(finger);
                }
                AstPathPartKw::Crate => {
                    return Ok(local_crate_root);
                }
                AstPathPartKw::Super => {
                    let Some(parent) = resolver.direct_parent(finger) else {
                        return Err(StepResolveError::CannotSuperInRoot);
                    };

                    return Ok(parent);
                }
            }
        }
        AstPathPartKind::Regular(ident) => ident,
    };

    // Attempt to resolve a direct link.
    match resolver.lookup_direct(vis_ctxt, finger, part.text) {
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
        if !reentrant_glob_lookups.insert(finger) {
            break 'glob_import;
        }

        // Collect resolutions
        let mut first_resolution = None::<(R::Item, Span)>;

        for use_idx in 0..resolver.global_use_count(finger) {
            let target = match resolver.global_use_target(vis_ctxt, finger, use_idx) {
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
                    | StepResolveError::CannotKeywordOnNonModule(_),
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

            let resolution_span = resolver.global_use_span(finger, use_idx);

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

        reentrant_glob_lookups.remove(&finger);

        // Ensure that our resolution is unambiguous.
        let Some((first, _first_span)) = first_resolution else {
            break 'glob_import;
        };

        return Ok(first);
    }

    // Nothing could provide this path part!
    Err(StepResolveError::NotFound)
}
