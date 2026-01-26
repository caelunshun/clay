use crate::{
    base::{
        Diag, ErrorGuaranteed, LeafDiag, Level,
        analysis::SpannedViewEncode,
        arena::{HasListInterner, Obj},
        syntax::{HasSpan as _, Span},
    },
    parse::{
        ast::{
            AstBarePath, AstNamedSpec, AstTraitClause, AstTraitClauseList, AstTraitOutlivesClause,
            AstTy, AstTyKind, AstTyOrRe, OutlivesKind,
        },
        token::Lifetime,
    },
    semantic::{
        lower::{
            entry::IntraItemLowerCtxt,
            modules::{FrozenModuleResolver, PathResolver as _},
        },
        syntax::{
            AdtItem, Item, ItemKind, Re, RelationDirection, SpannedAdtInstanceView,
            SpannedHrtbBinderKindView, SpannedHrtbBinderView, SpannedRe, SpannedTraitClause,
            SpannedTraitClauseList, SpannedTraitClauseView, SpannedTraitParamList,
            SpannedTraitSpec, SpannedTraitSpecView, SpannedTy, SpannedTyList, SpannedTyOrRe,
            SpannedTyOrReView, SpannedTyProjectionView, SpannedTyView, TraitItem, TypeGeneric,
        },
    },
    symbol,
};

// === Name Resolution === //

#[derive(Debug, Copy, Clone)]
pub enum TyPathResolution {
    Generic(Obj<TypeGeneric>),
    Adt(Obj<AdtItem>),
    Trait(Obj<TraitItem>),
    Other(Obj<Item>),
}

impl IntraItemLowerCtxt<'_> {
    pub fn resolve_ty_item_path(
        &self,
        path: &AstBarePath,
    ) -> Result<TyPathResolution, ErrorGuaranteed> {
        let s = &self.tcx.session;
        let mut resolver = FrozenModuleResolver(s);

        if let Some(first) = path.parts.first()
            && let Some(first) = first.ident()
            && let Some(generic) = self.generic_ty_names.lookup(first.text)
        {
            if let Some(subsequent) = path.parts.get(1) {
                Diag::span_err(
                    subsequent.span(),
                    "generic types cannot be accessed like modules",
                )
                .emit();
            }

            return Ok(TyPathResolution::Generic(*generic));
        }

        let target = resolver.resolve_bare_path(self.root, self.scope, path)?;

        match *target.r(s).kind {
            ItemKind::Adt(def) => Ok(TyPathResolution::Adt(def)),
            ItemKind::Trait(def) => Ok(TyPathResolution::Trait(def)),
            _ => Ok(TyPathResolution::Other(target)),
        }
    }

    pub fn resolve_ty_item_path_as_trait(
        &self,
        path: &AstBarePath,
    ) -> Result<Obj<TraitItem>, ErrorGuaranteed> {
        let s = &self.tcx.session;

        let offending_item = match self.resolve_ty_item_path(path)? {
            TyPathResolution::Trait(def) => return Ok(def),
            TyPathResolution::Generic(_) => {
                return Err(
                    Diag::span_err(path.span, "expected type, found generic parameter").emit(),
                );
            }
            TyPathResolution::Adt(def) => def.r(s).item,
            TyPathResolution::Other(item) => item,
        };

        Err(Diag::span_err(
            path.span,
            format_args!(
                "expected trait, found {}",
                offending_item.r(s).bare_category_path(s),
            ),
        )
        .emit())
    }
}

// === Type Lowering === //

impl IntraItemLowerCtxt<'_> {
    pub fn lower_ty_or_re(&mut self, ast: &AstTyOrRe) -> SpannedTyOrRe {
        match ast {
            AstTyOrRe::Re(ast) => {
                SpannedTyOrReView::Re(self.lower_re(ast)).encode(ast.span, self.tcx)
            }
            AstTyOrRe::Ty(ast) => {
                SpannedTyOrReView::Ty(self.lower_ty(ast)).encode(ast.span, self.tcx)
            }
        }
    }

    pub fn lower_re(&mut self, ast: &Lifetime) -> SpannedRe {
        if let Some(generic) = self.generic_re_names.lookup(ast.name) {
            return Re::SigGeneric(*generic).encode(ast.span, self.tcx);
        }

        // TODO: Use actual keyword lifetimes
        if ast.name == symbol!("gc") {
            return Re::Gc.encode(ast.span, self.tcx);
        }

        todo!()
    }

    pub fn lower_opt_ty(&mut self, ast: Option<&AstTy>) -> Option<SpannedTy> {
        ast.map(|ast| self.lower_ty(ast))
    }

    pub fn lower_ty(&mut self, ast: &AstTy) -> SpannedTy {
        let s = &self.tcx.session;

        match &ast.kind {
            AstTyKind::This => SpannedTyView::SigThis.encode(ast.span, self.tcx),
            AstTyKind::Name(path, generics) => {
                let resolver = FrozenModuleResolver(s);

                match self.resolve_ty_item_path(path) {
                    Ok(TyPathResolution::Adt(def)) => {
                        let params = self.lower_generics_of_entirely_positional(
                            def.r(s).item,
                            def.r(s).generics,
                            ast.span,
                            generics.as_ref().map_or(&[][..], |v| &v.list),
                        );

                        SpannedTyView::Adt(
                            SpannedAdtInstanceView { def, params }.encode(ast.span, self.tcx),
                        )
                        .encode(ast.span, self.tcx)
                    }
                    Ok(TyPathResolution::Generic(def)) => {
                        SpannedTyView::SigGeneric(def).encode(ast.span, self.tcx)
                    }
                    Ok(TyPathResolution::Trait(def)) => SpannedTyView::Error(
                        Diag::span_err(
                            ast.span,
                            format_args!(
                                "expected a struct or enum, found trait `{}`",
                                resolver.path(def.r(s).item),
                            ),
                        )
                        .child(LeafDiag::new(
                            Level::Help,
                            "consider prefixing the trait with `dyn`",
                        ))
                        .emit(),
                    )
                    .encode(ast.span, self.tcx),
                    Ok(TyPathResolution::Other(def)) => SpannedTyView::Error(
                        Diag::span_err(
                            ast.span,
                            format_args!(
                                "expected a struct or enum, found {}",
                                def.r(s).bare_category_path(s),
                            ),
                        )
                        .emit(),
                    )
                    .encode(ast.span, self.tcx),
                    Err(err) => SpannedTyView::Error(err).encode(ast.span, self.tcx),
                }
            }
            AstTyKind::Reference(lifetime, muta, pointee) => SpannedTyView::Reference(
                match lifetime {
                    Some(ast) => self.lower_re(ast),
                    None => Re::SigInfer.encode(ast.span.shrink_to_lo(), self.tcx),
                },
                muta.as_muta(),
                self.lower_ty(pointee),
            )
            .encode(ast.span, self.tcx),
            AstTyKind::Trait(lifetime, muta, spec) => SpannedTyView::Trait(
                match lifetime {
                    Some(ast) => self.lower_re(ast),
                    None => Re::SigInfer.encode(ast.span.shrink_to_lo(), self.tcx),
                },
                muta.as_muta(),
                self.lower_clauses(Some(spec)),
            )
            .encode(ast.span, self.tcx),
            AstTyKind::Paren(ast) => self.lower_ty(ast),
            AstTyKind::Tuple(items) => {
                SpannedTyView::Tuple(self.lower_tys(items)).encode(ast.span, self.tcx)
            }
            AstTyKind::Project(target, spec, assoc) => {
                let target = self.lower_ty(target);
                let spec = match self.lower_trait_spec(spec) {
                    Ok(spec) => spec,
                    Err(error) => return SpannedTyView::Error(error).encode(ast.span, self.tcx),
                };

                let Some(assoc_generic) = spec.value.def.r(s).associated_types.get(&assoc.text)
                else {
                    return SpannedTyView::Error(
                        Diag::span_err(assoc.span, "no such associated type").emit(),
                    )
                    .encode(ast.span, self.tcx);
                };

                SpannedTyView::SigProject(
                    SpannedTyProjectionView {
                        target,
                        spec,
                        assoc_span: Some(assoc.span),
                        assoc: assoc_generic.r(s).binder.idx,
                    }
                    .encode(ast.span, self.tcx),
                )
                .encode(ast.span, self.tcx)
            }
            AstTyKind::Infer => SpannedTyView::SigInfer.encode(ast.span, self.tcx),
            AstTyKind::Error(error) => SpannedTyView::Error(*error).encode(ast.span, self.tcx),
        }
    }

    pub fn lower_tys(&mut self, ast: &[AstTy]) -> SpannedTyList {
        SpannedTyList::alloc_list(
            Span::DUMMY,
            &ast.iter().map(|ast| self.lower_ty(ast)).collect::<Vec<_>>(),
            self.tcx,
        )
    }
}

// === Trait Clause Lowering === //

impl IntraItemLowerCtxt<'_> {
    pub fn lower_clauses(&mut self, ast: Option<&AstTraitClauseList>) -> SpannedTraitClauseList {
        let Some(ast) = ast else {
            return SpannedTraitClauseList::new_unspanned(self.tcx.intern_list(&[]));
        };

        let mut clauses = Vec::new();

        for ast in &ast.clauses {
            let Ok(ast) = ast else {
                continue;
            };

            let Ok(clause) = self.lower_clause(ast) else {
                continue;
            };

            clauses.push(clause);
        }

        SpannedTraitClauseList::alloc_list(ast.span, &clauses, self.tcx)
    }

    pub fn lower_clause(
        &mut self,
        ast: &AstTraitClause,
    ) -> Result<SpannedTraitClause, ErrorGuaranteed> {
        let tcx = self.tcx;

        match ast {
            AstTraitClause::Outlives(AstTraitOutlivesClause { span, kind, other }) => {
                Ok(SpannedTraitClauseView::Outlives(
                    match kind {
                        OutlivesKind::Shorter => RelationDirection::RhsOntoLhs,
                        OutlivesKind::Longer => RelationDirection::LhsOntoRhs,
                    },
                    self.lower_ty_or_re(other),
                )
                .encode(*span, self.tcx))
            }
            AstTraitClause::Trait(spec) => {
                let binder =
                    self.lower_complete_param_list(spec.binder.as_ref().map(|v| &v.params));

                let binder_span = spec.binder.as_ref().map_or(spec.span, |v| v.span);

                let inner = self.scoped(|this| {
                    this.define_generics_in_binder(binder);
                    this.lower_trait_spec(&spec.spec)
                })?;

                Ok(SpannedTraitClauseView::Trait(
                    SpannedHrtbBinderView {
                        kind: SpannedHrtbBinderKindView::Signature(binder).encode(binder_span, tcx),
                        inner,
                    }
                    .encode(spec.span, tcx),
                )
                .encode(spec.span, self.tcx))
            }
        }
    }

    pub fn lower_trait_spec(
        &mut self,
        ast: &AstNamedSpec,
    ) -> Result<SpannedTraitSpec, ErrorGuaranteed> {
        let s = &self.tcx.session;

        // Figure out which trait we're talking about.
        let def = self.resolve_ty_item_path_as_trait(&ast.path)?;

        // Lower generic parameters.
        let (positional, associated) =
            self.lower_generic_params_syntactic(ast.params.as_ref().map_or(&[][..], |v| &v.list));

        let params = self.normalize_positional_generic_arity(
            def.r(s).generics,
            Some(def.r(s).regular_generic_count),
            ast.span,
            &positional,
        );
        let mut params = self.construct_trait_spec_from_positionals(def, params, ast.span);

        self.lower_associated_type_generic_params(def, &mut params, &associated);

        let params = SpannedTraitParamList::alloc_list(ast.span, &params, self.tcx);

        Ok(SpannedTraitSpecView { def, params }.encode(ast.span, self.tcx))
    }
}
