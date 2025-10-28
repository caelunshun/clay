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
    utils::hash::FxHashMap,
};
use hashbrown::hash_map;
use index_vec::{IndexVec, define_index_type};
use std::mem;

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
    direct_items: FxHashMap<Symbol, DirectItem<T>>,
    glob_lookup_cache: FxHashMap<Symbol, ModuleResolution<T>>,
}

struct GlobImport<T> {
    span: Span,
    visibility: Visibility<T>,
    path: AstSimplePath,
}

struct DirectItem<T> {
    name: Ident,
    visibility: Visibility<T>,
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

struct Visibility<T> {
    span: Span,
    kind: VisibilityKind<T>,
}

enum VisibilityKind<T> {
    Priv,
    Pub,
    PubIn(CachedPath<T>),
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
                direct_items: FxHashMap::default(),
                glob_lookup_cache: FxHashMap::default(),
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
            hash_map::Entry::Vacant(entry) => {
                entry.insert(direct);
                Ok(())
            }
            hash_map::Entry::Occupied(entry) => Err(Diag::span_err(
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
            direct_items: FxHashMap::default(),
            glob_lookup_cache: FxHashMap::default(),
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
            path,
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

    pub fn freeze_and_check(&mut self) {
        debug_assert!(!self.frozen);

        // Begin by determining public paths for each module.
        // TODO

        // Next, normalize all visibilities.
        // TODO

        // Now, check each module's use paths.
        // TODO
    }

    pub fn resolve(
        &mut self,
        within: ModuleId,
        path: &AstSimplePath,
    ) -> Result<ModuleResolution<T>, ErrorGuaranteed> {
        debug_assert!(self.frozen);

        self.resolve_inner(within, path)
    }

    fn resolve_inner(
        &mut self,
        within: ModuleId,
        path: &AstSimplePath,
    ) -> Result<ModuleResolution<T>, ErrorGuaranteed> {
        let mut finger = ModuleResolution::Module(within);

        let mut parts_iter = path.parts.iter();

        while let (Some(part), &ModuleResolution::Module(curr)) = (parts_iter.next(), &finger) {
            // Handle special path parts.
            if part.matches_kw(symbol!("self")) {
                // (leave `curr` unchanged)
                continue;
            }

            if part.matches_kw(symbol!("crate")) {
                finger = ModuleResolution::Module(ModuleId::ROOT);
                continue;
            }

            if part.matches_kw(symbol!("super")) {
                let Some(parent) = self.modules[curr].parent else {
                    return Err(
                        Diag::span_err(part.span, "`super` cannot apply to crate root").emit(),
                    );
                };

                finger = ModuleResolution::Module(parent);
                continue;
            }

            // Attempt to resolve a direct link.
            if let Some(item) = self.modules[curr].direct_items.get_mut(&part.text) {
                // Check visibility
                match &item.visibility.kind {
                    VisibilityKind::Priv => {
                        // TODO: Error
                    }
                    VisibilityKind::Pub => {
                        // (fallthrough)
                    }
                    VisibilityKind::PubIn(CachedPath::Resolved(ModuleResolution::Module(
                        visible_to,
                    ))) => {
                        // TODO
                    }
                    VisibilityKind::PubIn(_) => unreachable!(),
                }

                // Find resolution. This may require resolving an unresolved path if we're still in
                // the freeze-and-check phase.
                match &mut item.kind {
                    DirectItemKind::Link(CachedPath::Ignore) => {
                        // We cannot use a `use` in its own resolution.
                        // (fallthrough)
                    }
                    DirectItemKind::Link(CachedPath::Unresolved(_)) => {
                        let DirectItemKind::Link(CachedPath::Unresolved(path)) =
                            mem::replace(&mut item.kind, DirectItemKind::Link(CachedPath::Ignore))
                        else {
                            unreachable!()
                        };

                        if let Ok(resolution) = self.resolve_inner(within, &path) {
                            // Record the resolution.
                            self.modules[curr]
                                .direct_items
                                .get_mut(&part.text)
                                .unwrap()
                                .kind =
                                DirectItemKind::Link(CachedPath::Resolved(resolution.clone()));

                            finger = resolution;

                            continue;
                        } else {
                            // Let the path part stay as `Ignore` since it couldn't resolve to
                            // anything.
                            // (fallthrough)
                        }
                    }
                    DirectItemKind::Link(CachedPath::Resolved(resolution)) => {
                        finger = resolution.clone();
                        continue;
                    }
                    DirectItemKind::Item(item) => {
                        finger = ModuleResolution::Item(item.clone());
                        continue;
                    }
                };
            }

            // Otherwise, attempt to follow a global import.
            if let Some(cached) = self.modules[curr].glob_lookup_cache.get(&part.text) {
                finger = cached.clone();
                continue;
            }

            // TODO

            // Nothing could provide this path part!
            return Err(Diag::span_err(
                part.span,
                format_args!(
                    // TODO: Prefix
                    "`{}` not found in `{}`",
                    part.text,
                    self.modules[curr].public_path.unwrap(),
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
                        path.parts[path.parts.len() - parts_iter.len() - 1].span,
                        "not a module",
                    )
                    .emit())
                }
            }
        }
    }
}

impl<T> From<AstVisibility> for Visibility<T> {
    fn from(visibility: AstVisibility) -> Self {
        let kind = match visibility.kind {
            AstVisibilityKind::Implicit | AstVisibilityKind::Priv => VisibilityKind::Priv,
            AstVisibilityKind::Pub => VisibilityKind::Pub,
            AstVisibilityKind::PubIn(path) => VisibilityKind::PubIn(CachedPath::Unresolved(path)),
        };

        Visibility {
            span: visibility.span,
            kind,
        }
    }
}
