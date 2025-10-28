use crate::{
    base::{
        Diag, ErrorGuaranteed, LeafDiag,
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
    Item(T),
}

struct Module<T> {
    parent: Option<ModuleId>,
    name: Option<Ident>,
    public_path: Option<Symbol>,
    outer_span: Span,
    inner_span: Span,
    glob_imports: Vec<GlobImport<T>>,
    direct_items: FxIndexMap<Symbol, DirectItem<T>>,
    glob_lookup_cache: FxIndexMap<Symbol, ModuleResolution<T>>,
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

struct Visibility {
    span: Span,
    kind: VisibilityKind,
}

enum VisibilityKind {
    Priv,
    Pub,
    PubInResolved(ModuleId),
    PubInUnresolved(AstSimplePath),
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
enum ResolverMode {
    Visibility,
    Solve,
    Lookup,
}

impl<T: Clone> ModuleTree<T> {
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
                glob_lookup_cache: FxIndexMap::default(),
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
            glob_lookup_cache: FxIndexMap::default(),
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
        target: ModuleId,
        suffix: Option<Symbol>,
    ) -> impl 'static + Copy + fmt::Display {
        #[derive(Copy, Clone)]
        struct ModulePathFmt {
            prefix: Symbol,
            main_part: Symbol,
            suffix: Option<Symbol>,
        }

        impl fmt::Display for ModulePathFmt {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                todo!()
            }
        }

        ModulePathFmt {
            prefix,
            main_part: self.modules[target].public_path.unwrap(),
            suffix,
        }
    }

    pub fn freeze_and_check(&mut self) {
        debug_assert!(!self.frozen);
        self.frozen = true;

        // Begin by determining public paths for each module.
        // TODO

        // Next, normalize all visibilities.
        for module_id in self.modules.indices() {
            fn resolve_visibility<T: Clone>(
                tree: &mut ModuleTree<T>,
                within: ModuleId,
                fetch: impl Fn(&mut ModuleTree<T>) -> &mut Visibility,
            ) {
                let vis = &mut fetch(tree).kind;

                if !matches!(vis, VisibilityKind::PubInUnresolved(_)) {
                    return;
                }

                let VisibilityKind::PubInUnresolved(path) = mem::replace(vis, VisibilityKind::Pub)
                else {
                    return;
                };

                let target = match tree.resolve_inner(within, &path.parts, ResolverMode::Visibility)
                {
                    Ok(ModuleResolution::Module(target)) => target,
                    Ok(ModuleResolution::Item(_)) => {
                        _ = Diag::span_err(
                            path.parts.last().unwrap().span,
                            "must refer to a module",
                        )
                        .emit();

                        // (leave the visibility as `pub`)
                        return;
                    }
                    Err(_) => {
                        // (leave the visibility as `pub`)
                        return;
                    }
                };

                if !tree.is_descendant(within, target) {
                    _ = Diag::span_err(path.span, "not an ancestor of the current module").emit();

                    // (leave the visibility as `pub`)
                    return;
                }

                fetch(tree).kind = VisibilityKind::PubInResolved(target);
            }

            for use_idx in 0..self.modules[module_id].direct_items.len() {
                resolve_visibility(self, module_id, |tree| {
                    &mut tree.modules[module_id].direct_items[use_idx].visibility
                });
            }

            for use_idx in 0..self.modules[module_id].glob_imports.len() {
                resolve_visibility(self, module_id, |tree| {
                    &mut tree.modules[module_id].glob_imports[use_idx].visibility
                });
            }
        }

        // Finally, resolve each module's use paths.
        for module_id in self.modules.indices() {
            fn resolve_path<T: Clone>(
                tree: &mut ModuleTree<T>,
                within: ModuleId,
                fetch: impl Fn(&mut ModuleTree<T>) -> &mut CachedPath<T>,
            ) {
                let path = fetch(tree);

                if !matches!(path, CachedPath::Unresolved(_)) {
                    return;
                }

                let CachedPath::Unresolved(path) = mem::replace(path, CachedPath::Ignore) else {
                    return;
                };

                let Ok(target) = tree.resolve_inner(within, &path.parts, ResolverMode::Solve)
                else {
                    // (leave the path as `Ignore`)
                    return;
                };

                *fetch(tree) = CachedPath::Resolved(target);
            }

            for use_idx in 0..self.modules[module_id].direct_items.len() {
                if !matches!(
                    self.modules[module_id].direct_items[use_idx].kind,
                    DirectItemKind::Link(_)
                ) {
                    continue;
                }

                resolve_path(self, module_id, |tree| {
                    let DirectItemKind::Link(v) =
                        &mut tree.modules[module_id].direct_items[use_idx].kind
                    else {
                        unreachable!()
                    };

                    v
                });
            }

            for use_idx in 0..self.modules[module_id].glob_imports.len() {
                resolve_path(self, module_id, |tree| {
                    &mut tree.modules[module_id].glob_imports[use_idx].path
                });
            }
        }
    }

    pub fn resolve(
        &mut self,
        within: ModuleId,
        path: &AstSimplePath,
    ) -> Result<ModuleResolution<T>, ErrorGuaranteed> {
        debug_assert!(self.frozen);

        self.resolve_inner(within, &path.parts, ResolverMode::Lookup)
    }

    fn resolve_inner(
        &mut self,
        within: ModuleId,
        path: &[Ident],
        mode: ResolverMode,
    ) -> Result<ModuleResolution<T>, ErrorGuaranteed> {
        let mut finger = ModuleResolution::Module(within);

        let mut parts_iter = path.iter();

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
                    return Err(
                        Diag::span_err(part.span, "`super` cannot apply to crate root").emit(),
                    );
                };

                finger = ModuleResolution::Module(parent);
                continue 'traverse;
            }

            // Attempt to resolve a direct link.
            if let Some(item) = self.modules[curr].direct_items.get_mut(&part.text) {
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
                            if self.is_descendant(within, visible_to) {
                                break 'vis_check;
                            }

                            // (fallthrough)
                        }
                        VisibilityKind::PubInUnresolved(_) => unreachable!(),
                    }

                    // The check failed!
                    return Err(Diag::span_err(
                        part.span,
                        "item is not visible to the current module",
                    )
                    .emit());
                }

                // Find resolution. This may require resolving an unresolved path if we're still in
                // the freeze-and-check phase.
                let item = self.modules[curr].direct_items.get_mut(&part.text).unwrap();

                match &mut item.kind {
                    DirectItemKind::Link(CachedPath::Ignore) => {
                        // We cannot use a `use` in its own resolution.
                        // (fallthrough)
                    }
                    DirectItemKind::Link(CachedPath::Unresolved(_)) => 'resolve: {
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
                                break 'resolve;
                            }
                            ResolverMode::Solve => {
                                // (fallthrough)
                            }
                            ResolverMode::Lookup => unreachable!(),
                        }

                        let DirectItemKind::Link(CachedPath::Unresolved(path)) =
                            mem::replace(&mut item.kind, DirectItemKind::Link(CachedPath::Ignore))
                        else {
                            unreachable!()
                        };

                        if let Ok(resolution) = self.resolve_inner(within, &path.parts, mode) {
                            // Record the resolution.
                            self.modules[curr]
                                .direct_items
                                .get_mut(&part.text)
                                .unwrap()
                                .kind =
                                DirectItemKind::Link(CachedPath::Resolved(resolution.clone()));

                            finger = resolution;

                            continue 'traverse;
                        } else {
                            // Let the path part stay as `Ignore` since it couldn't resolve to
                            // anything.
                            // (fallthrough)
                        }
                    }
                    DirectItemKind::Link(CachedPath::Resolved(resolution)) => {
                        finger = resolution.clone();
                        continue 'traverse;
                    }
                    DirectItemKind::Item(item) => {
                        finger = ModuleResolution::Item(item.clone());
                        continue 'traverse;
                    }
                };
            }

            // Otherwise, attempt to follow a global import.
            if mode != ResolverMode::Visibility {
                if let Some(cached) = self.modules[curr].glob_lookup_cache.get(&part.text) {
                    finger = cached.clone();
                    continue 'traverse;
                }

                // let mut resolutions = Vec::new();
                //
                // for import in self.modules[curr].glob_imports {
                //     self.resolve_inner(within, &[*part], mode);
                // }

                // TODO
            }

            // Nothing could provide this path part!
            return Err(Diag::span_err(
                part.span,
                format_args!(
                    "`{}` not found in `{}`",
                    part.text,
                    self.module_path(symbol!("crate"), curr, None),
                ),
            )
            .emit());
        }

        match finger {
            v @ ModuleResolution::Module(_) => Ok(v),
            ModuleResolution::Item(item) => {
                if parts_iter.len() == 0 {
                    Ok(ModuleResolution::Item(item.clone()))
                } else {
                    Err(Diag::span_err(
                        path[path.len() - parts_iter.len() - 1].span,
                        "not a module",
                    )
                    .emit())
                }
            }
        }
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
