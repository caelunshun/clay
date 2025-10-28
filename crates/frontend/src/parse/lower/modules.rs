use crate::{
    base::{
        Diag, ErrorGuaranteed, LeafDiag, Session,
        syntax::{Span, Symbol},
    },
    parse::{
        ast::{AstSimplePath, AstVisibility, AstVisibilityKind},
        token::Ident,
    },
    symbol,
    utils::hash::FxIndexMap,
};
use index_vec::{IndexVec, define_index_type};
use std::{fmt, mem};

// === ModuleTree === //

define_index_type! {
    pub struct ModuleId = u32;
}

impl ModuleId {
    pub const ROOT: Self = ModuleId { _raw: 0 };
}

pub struct ModuleTree<T> {
    modules: IndexVec<ModuleId, Module<T>>,
    frozen: bool,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum ModuleResolution<T> {
    Module(ModuleId),
    Item(ItemResolution<T>),
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct ItemResolution<T> {
    pub owner: ModuleId,
    pub name: Symbol,
    pub value: T,
}

struct Module<T> {
    parent: Option<ModuleId>,
    name: Option<Ident>,
    public_path: Option<Symbol>,
    outer_span: Span,
    inner_span: Span,
    glob_imports: Vec<GlobImport<T>>,
    direct_items: FxIndexMap<Symbol, DirectItem<T>>,
    actively_performing_glob_resolution: bool,
}

struct GlobImport<T> {
    span: Span,
    visibility: Visibility,
    path: CachedPath<T>,
}

struct DirectItem<T> {
    name: Ident,
    visibility: Visibility,
    kind: DirectItemKind<T>,
}

enum DirectItemKind<T> {
    Link(CachedPath<T>),
    Item(T),
}

enum CachedPath<T> {
    Ignore,
    Unresolved(AstSimplePath),
    Resolved(ModuleResolution<T>),
}

#[derive(Clone)]
struct Visibility {
    span: Span,
    kind: VisibilityKind,
}

#[derive(Clone)]
enum VisibilityKind {
    Priv,
    Pub,
    PubInResolved(ModuleId),
    PubInUnresolved(AstSimplePath),
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
enum ResolverMode {
    /// Don't follow global imports, ignore visibility, and ignore unresolved imports (i.e.
    /// everything that's not a module ownership link).
    Visibility,

    /// Follow everything, keep visibility in mind, and resolve unresolved imports.
    Solve,

    /// Follow everything, keep visibility in mind, and panic on unresolved imports since they
    /// shouldn't exist at this stage.
    Lookup,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
enum EmitErrors {
    Yes,
    No,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
enum MustBeModule {
    Yes,
    No,
}

impl<T: Clone + Eq> ModuleTree<T> {
    pub fn new(root_span: Span) -> Self {
        Self {
            modules: IndexVec::from_iter([Module {
                parent: None,
                name: None,
                public_path: None,
                outer_span: root_span,
                inner_span: root_span,
                glob_imports: Vec::new(),
                direct_items: FxIndexMap::default(),
                actively_performing_glob_resolution: false,
            }]),
            frozen: false,
        }
    }

    fn push_direct(
        &mut self,
        target: ModuleId,
        direct: DirectItem<T>,
    ) -> Result<(), ErrorGuaranteed> {
        debug_assert!(!self.frozen);

        match self.modules[target].direct_items.entry(direct.name.text) {
            indexmap::map::Entry::Vacant(entry) => {
                entry.insert(direct);
                Ok(())
            }
            indexmap::map::Entry::Occupied(entry) => Err(Diag::span_err(
                direct.name.span,
                format_args!("name `{}` used more than once in module", direct.name.text),
            )
            .child(LeafDiag::span_note(
                entry.get().name.span,
                "name previously used here",
            ))
            .emit()),
        }
    }

    pub fn push_module(
        &mut self,
        parent: ModuleId,
        visibility: AstVisibility,
        name: Ident,
        outer_span: Span,
        inner_span: Span,
    ) -> (ModuleId, Result<(), ErrorGuaranteed>) {
        debug_assert!(!self.frozen);

        let child = self.modules.push(Module {
            parent: Some(parent),
            name: Some(name),
            public_path: None,
            outer_span,
            inner_span,
            glob_imports: Vec::new(),
            direct_items: FxIndexMap::default(),
            actively_performing_glob_resolution: false,
        });

        let err = self.push_direct(
            parent,
            DirectItem {
                name,
                visibility: visibility.into(),
                kind: DirectItemKind::Link(CachedPath::Resolved(ModuleResolution::Module(child))),
            },
        );

        (child, err)
    }

    pub fn push_glob_use(
        &mut self,
        parent: ModuleId,
        visibility: AstVisibility,
        span: Span,
        path: AstSimplePath,
    ) {
        debug_assert!(!self.frozen);

        self.modules[parent].glob_imports.push(GlobImport {
            span,
            visibility: visibility.into(),
            path: CachedPath::Unresolved(path),
        });
    }

    pub fn push_single_use(
        &mut self,
        parent: ModuleId,
        visibility: AstVisibility,
        name: Ident,
        path: AstSimplePath,
    ) -> Result<(), ErrorGuaranteed> {
        debug_assert!(!self.frozen);

        self.push_direct(
            parent,
            DirectItem {
                name,
                visibility: visibility.into(),
                kind: DirectItemKind::Link(CachedPath::Unresolved(path)),
            },
        )
    }

    pub fn push_item(
        &mut self,
        parent: ModuleId,
        visibility: AstVisibility,
        name: Ident,
        data: T,
    ) -> Result<(), ErrorGuaranteed> {
        debug_assert!(!self.frozen);

        self.push_direct(
            parent,
            DirectItem {
                name,
                visibility: visibility.into(),
                kind: DirectItemKind::Item(data),
            },
        )
    }

    pub fn module_path(
        &self,
        prefix: Symbol,
        target: ModuleResolution<T>,
    ) -> impl 'static + Copy + fmt::Display {
        #[derive(Copy, Clone)]
        struct ModulePathFmt {
            prefix: Symbol,
            main_part: Symbol,
            suffix: Option<Symbol>,
        }

        impl fmt::Display for ModulePathFmt {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let s = &Session::fetch();

                let parts = [
                    self.prefix.as_str(s),
                    self.main_part.as_str(s),
                    self.suffix.map_or("", |sym| sym.as_str(s)),
                ];

                let mut wrote_something = false;

                for part in parts {
                    if part.is_empty() {
                        continue;
                    }

                    if wrote_something {
                        f.write_str("::")?;
                    }

                    f.write_str(part)?;
                    wrote_something = true;
                }

                Ok(())
            }
        }

        let (main_part, suffix) = match target {
            ModuleResolution::Module(module) => (module, None),
            ModuleResolution::Item(ItemResolution {
                owner,
                name,
                value: _,
            }) => (owner, Some(name)),
        };

        ModulePathFmt {
            prefix,
            main_part: self.modules[main_part].public_path.unwrap(),
            suffix,
        }
    }

    pub fn freeze_and_check(&mut self) {
        debug_assert!(!self.frozen);
        self.frozen = true;

        // Begin by determining public paths for each module.
        // TODO: improve this algorithm.
        for module_id in self.modules.indices() {
            let s = &Session::fetch();

            let mut parts = Vec::new();
            let mut finger = Some(module_id);

            while let Some(curr) = finger {
                let curr = &self.modules[curr];

                if let Some(name) = curr.name {
                    parts.push(name.text.as_str(s));
                } else {
                    debug_assert!(curr.parent.is_none());
                }

                finger = curr.parent;
            }

            parts.reverse();

            self.modules[module_id].public_path = Some(Symbol::new(&parts.join("::")));
        }

        // Next, normalize all visibilities.
        for module_id in self.modules.indices() {
            for use_idx in 0..self.modules[module_id].direct_items.len() {
                self.resolve_visibility(module_id, |tree| {
                    &mut tree.modules[module_id].direct_items[use_idx].visibility
                });
            }

            for use_idx in 0..self.modules[module_id].glob_imports.len() {
                self.resolve_visibility(module_id, |tree| {
                    &mut tree.modules[module_id].glob_imports[use_idx].visibility
                });
            }
        }

        // Finally, resolve each module's use paths.
        for module_id in self.modules.indices() {
            for use_idx in 0..self.modules[module_id].direct_items.len() {
                if !matches!(
                    self.modules[module_id].direct_items[use_idx].kind,
                    DirectItemKind::Link(_)
                ) {
                    continue;
                }

                _ = self.resolve_path(
                    module_id,
                    |tree| {
                        let DirectItemKind::Link(v) =
                            &mut tree.modules[module_id].direct_items[use_idx].kind
                        else {
                            unreachable!()
                        };

                        v
                    },
                    ResolverMode::Solve,
                    MustBeModule::No,
                );
            }

            for use_idx in 0..self.modules[module_id].glob_imports.len() {
                _ = self.resolve_path(
                    module_id,
                    |tree| &mut tree.modules[module_id].glob_imports[use_idx].path,
                    ResolverMode::Solve,
                    MustBeModule::Yes,
                );
            }
        }
    }

    pub fn resolve(
        &mut self,
        within: ModuleId,
        path: &AstSimplePath,
    ) -> Result<ModuleResolution<T>, ErrorGuaranteed> {
        debug_assert!(self.frozen);

        self.resolve_inner(
            within,
            within,
            &path.parts,
            ResolverMode::Lookup,
            EmitErrors::Yes,
        )
        .map_err(Option::unwrap)
    }

    fn resolve_inner(
        &mut self,
        visibility_cx: ModuleId,
        finger: ModuleId,
        path: &[Ident],
        mode: ResolverMode,
        emit_errors: EmitErrors,
    ) -> Result<ModuleResolution<T>, Option<ErrorGuaranteed>> {
        let mut finger = ModuleResolution::Module(finger);

        let mut parts_iter = path.iter();

        fn make_err<T>(
            emit_errors: EmitErrors,
            f: impl FnOnce() -> Diag<ErrorGuaranteed>,
        ) -> Result<ModuleResolution<T>, Option<ErrorGuaranteed>> {
            match emit_errors {
                EmitErrors::Yes => Err(Some(f().emit())),
                EmitErrors::No => Err(None),
            }
        }

        'traverse: while let (Some(part), &ModuleResolution::Module(curr)) =
            (parts_iter.next(), &finger)
        {
            // Handle special path parts.
            if part.matches_kw(symbol!("self")) {
                // (leave `curr` unchanged)
                continue 'traverse;
            }

            if part.matches_kw(symbol!("crate")) {
                finger = ModuleResolution::Module(ModuleId::ROOT);
                continue 'traverse;
            }

            if part.matches_kw(symbol!("super")) {
                let Some(parent) = self.modules[curr].parent else {
                    return make_err(emit_errors, || {
                        Diag::span_err(part.span, "`super` cannot apply to crate root")
                    });
                };

                finger = ModuleResolution::Module(parent);
                continue 'traverse;
            }

            // Attempt to resolve a direct link.
            if let Some(item_idx) = self.modules[curr].direct_items.get_index_of(&part.text) {
                let item = &self.modules[curr].direct_items[item_idx];

                // Check visibility
                'vis_check: {
                    if mode == ResolverMode::Visibility {
                        break 'vis_check;
                    }

                    match item.visibility.kind {
                        VisibilityKind::Priv => {
                            // (fallthrough)
                        }
                        VisibilityKind::Pub => {
                            break 'vis_check;
                        }
                        VisibilityKind::PubInResolved(visible_to) => {
                            if self.is_descendant(visibility_cx, visible_to) {
                                break 'vis_check;
                            }

                            // (fallthrough)
                        }
                        VisibilityKind::PubInUnresolved(_) => unreachable!(),
                    }

                    // The check failed!
                    return make_err(emit_errors, || {
                        Diag::span_err(part.span, "item is not visible to the current module")
                    });
                }

                // Find resolution. This may require resolving an unresolved path if we're still in
                // the freeze-and-check phase.
                match &self.modules[curr].direct_items[item_idx].kind {
                    DirectItemKind::Link(_) => {
                        let resolution = self.resolve_path(
                            curr,
                            |tree| {
                                let DirectItemKind::Link(v) =
                                    &mut tree.modules[curr].direct_items[item_idx].kind
                                else {
                                    unreachable!()
                                };

                                v
                            },
                            mode,
                            MustBeModule::No,
                        );

                        if let Some(resolution) = resolution {
                            finger = resolution;
                            continue 'traverse;
                        }
                    }
                    DirectItemKind::Item(item) => {
                        finger = ModuleResolution::Item(ItemResolution {
                            owner: curr,
                            name: part.text,
                            value: item.clone(),
                        });
                        continue 'traverse;
                    }
                };
            }

            // Otherwise, attempt to follow a global import.
            'glob_import: {
                if mode == ResolverMode::Visibility {
                    break 'glob_import;
                }

                // Ensure that we're not reentrantly trying to glob-import from the same module.
                let curr_mod = &mut self.modules[curr];

                if curr_mod.actively_performing_glob_resolution {
                    break 'glob_import;
                }

                curr_mod.actively_performing_glob_resolution = true;

                // Collect resolutions
                let mut resolutions = Vec::new();

                for use_idx in 0..curr_mod.glob_imports.len() {
                    // Ensure that the glob-import is visible.
                    match self.modules[curr].glob_imports[use_idx].visibility.kind {
                        VisibilityKind::Priv => {
                            continue;
                        }
                        VisibilityKind::Pub => {
                            // (fallthrough)
                        }
                        VisibilityKind::PubInResolved(visible_to) => {
                            if !self.is_descendant(visibility_cx, visible_to) {
                                continue;
                            }

                            // (fallthrough)
                        }
                        VisibilityKind::PubInUnresolved(_) => unreachable!(),
                    }

                    // Determine what the glob-import is importing.
                    let resolution = self.resolve_path(
                        curr,
                        |tree| &mut tree.modules[curr].glob_imports[use_idx].path,
                        mode,
                        MustBeModule::Yes,
                    );

                    let Some(resolution) = resolution else {
                        continue;
                    };

                    let ModuleResolution::Module(resolution) = resolution else {
                        unreachable!()
                    };

                    // Attempt to resolve the item in that module.
                    if let Ok(resolution) = self.resolve_inner(
                        visibility_cx,
                        resolution,
                        &[*part],
                        mode,
                        EmitErrors::No,
                    ) {
                        let span = self.modules[curr].glob_imports[use_idx].span;

                        resolutions.push((resolution, span));
                    }
                }

                self.modules[curr].actively_performing_glob_resolution = false;

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
                                    self.module_path(symbol!("crate"), first.clone())
                                ),
                            ))
                            .child(LeafDiag::span_note(
                                *other_span,
                                format_args!(
                                    "second glob import resolves to `{}`",
                                    self.module_path(symbol!("crate"), other.clone())
                                ),
                            ))
                        });
                    }
                }

                finger = resolutions.into_iter().next().unwrap().0;
                continue 'traverse;
            }

            // Nothing could provide this path part!
            return make_err(emit_errors, || {
                Diag::span_err(
                    part.span,
                    format_args!(
                        "`{}` not found in `{}`",
                        part.text,
                        self.module_path(symbol!("crate"), finger),
                    ),
                )
            });
        }

        match finger {
            v @ ModuleResolution::Module(_) => Ok(v),
            ModuleResolution::Item(item) => {
                if parts_iter.len() == 0 {
                    Ok(ModuleResolution::Item(item.clone()))
                } else {
                    make_err(emit_errors, || {
                        Diag::span_err(path[path.len() - parts_iter.len() - 1].span, "not a module")
                    })
                }
            }
        }
    }

    fn resolve_path(
        &mut self,
        path_owner: ModuleId,
        fetch: impl Fn(&mut Self) -> &mut CachedPath<T>,
        mode: ResolverMode,
        must_be_module: MustBeModule,
    ) -> Option<ModuleResolution<T>> {
        let path = fetch(self);

        match path {
            CachedPath::Ignore => {
                return None;
            }
            CachedPath::Unresolved(_) => {
                match mode {
                    ResolverMode::Visibility => {
                        // We don't resolve unresolved paths while solving for visibility
                        // paths, effectively limiting us to referring to the module tree.
                        //
                        // This seems to be Rust's behavior as well. From [the spec]...
                        //
                        // ```
                        // pub(in path) makes an item visible within the provided path.
                        // path must be a simple path which resolves to an ancestor module
                        // of the item whose visibility is being declared. Each identifier
                        // in path must refer directly to a module (not to a name
                        // introduced by a use statement).
                        // ```
                        //
                        // [the spec]: https://doc.rust-lang.org/reference/visibility-and-privacy.html#r-vis.scoped.in
                        return None;
                    }
                    ResolverMode::Solve => {
                        // (fallthrough)
                    }
                    ResolverMode::Lookup => {
                        unreachable!()
                    }
                }
                // (fallthrough)
            }
            CachedPath::Resolved(resolved) => {
                return Some(resolved.clone());
            }
        }

        let CachedPath::Unresolved(path) = mem::replace(path, CachedPath::Ignore) else {
            unreachable!()
        };

        let Ok(target) = self.resolve_inner(
            path_owner,
            path_owner,
            &path.parts,
            ResolverMode::Solve,
            EmitErrors::Yes,
        ) else {
            // (leave the path as `Ignore`)
            return None;
        };

        match (must_be_module, &target) {
            (MustBeModule::Yes, ModuleResolution::Item(_)) => {
                Diag::span_err(path.span, "path must resolve to a module");

                // (leave the path as `Ignore`)
                return None;
            }
            (MustBeModule::Yes, ModuleResolution::Module(_)) | (MustBeModule::No, _) => {
                // (fallthrough)
            }
        }

        *fetch(self) = CachedPath::Resolved(target.clone());

        Some(target)
    }

    fn resolve_visibility(
        &mut self,
        within: ModuleId,
        fetch: impl Fn(&mut Self) -> &mut Visibility,
    ) {
        let vis = &mut fetch(self).kind;

        if !matches!(vis, VisibilityKind::PubInUnresolved(_)) {
            return;
        }

        let VisibilityKind::PubInUnresolved(path) = mem::replace(vis, VisibilityKind::Pub) else {
            return;
        };

        let target = match self.resolve_inner(
            within,
            within,
            &path.parts,
            ResolverMode::Visibility,
            EmitErrors::Yes,
        ) {
            Ok(ModuleResolution::Module(target)) => target,
            Ok(ModuleResolution::Item(_)) => {
                _ = Diag::span_err(path.parts.last().unwrap().span, "must refer to a module")
                    .emit();

                // (leave the visibility as `pub`)
                return;
            }
            Err(_) => {
                // (leave the visibility as `pub`)
                return;
            }
        };

        if target == within {
            fetch(self).kind = VisibilityKind::Priv;
            return;
        }

        if target == ModuleId::ROOT {
            // (leave the visibility as `pub`)
            return;
        }

        if !self.is_descendant(within, target) {
            _ = Diag::span_err(path.span, "not an ancestor of the current module").emit();

            // (leave the visibility as `pub`)
            return;
        }

        fetch(self).kind = VisibilityKind::PubInResolved(target);
    }

    pub fn is_descendant(&self, src: ModuleId, maybe_ancestor: ModuleId) -> bool {
        let mut finger = Some(src);

        while let Some(curr) = finger {
            if curr == maybe_ancestor {
                return true;
            }

            finger = self.modules[curr].parent;
        }

        false
    }
}

impl From<AstVisibility> for Visibility {
    fn from(visibility: AstVisibility) -> Self {
        let kind = match visibility.kind {
            AstVisibilityKind::Implicit | AstVisibilityKind::Priv => VisibilityKind::Priv,
            AstVisibilityKind::Pub => VisibilityKind::Pub,
            AstVisibilityKind::PubIn(path) => VisibilityKind::PubInUnresolved(path),
        };

        Visibility {
            span: visibility.span,
            kind,
        }
    }
}
