use crate::{
    base::{
        Diag, ErrorGuaranteed, LeafDiag, Level,
        arena::Obj,
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
            entry::{DefinedGenericRe, DefinedGenericTy, IntraItemLowerCtxt},
            modules::{FrozenModuleResolver, PathResolver as _},
        },
        syntax::{
            AdtItem, HrtbDebruijn, Item, ItemKind, RelationDirection, SigAdtInstance,
            SigHrtbBinder, SigProjectType, SigRe, SigReKind, SigTraitClause, SigTraitClauseKind,
            SigTraitClauseList, SigTraitParamList, SigTraitSpec, SigTy, SigTyKind, SigTyList,
            SigTyOrRe, TraitItem, TypeAliasItem, TypeGeneric,
        },
    },
    symbol,
};

// === Name Resolution === //

#[derive(Debug, Copy, Clone)]
pub enum TyPathResolution {
    GenericSig(Obj<TypeGeneric>),
    GenericHrtb(HrtbDebruijn),
    Adt(Obj<AdtItem>),
    Trait(Obj<TraitItem>),
    TypeAlias(Obj<TypeAliasItem>),
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

            return Ok(match *generic {
                DefinedGenericTy::Sig(generic) => TyPathResolution::GenericSig(generic),
                DefinedGenericTy::Hrtb(_span, pos) => TyPathResolution::GenericHrtb(HrtbDebruijn(
                    self.generic_debruijn.make_relative(pos),
                )),
            });
        }

        let target = resolver.resolve_bare_path(self.root, self.scope, path)?;

        match *target.r(s).kind {
            ItemKind::Adt(def) => Ok(TyPathResolution::Adt(def)),
            ItemKind::Trait(def) => Ok(TyPathResolution::Trait(def)),
            ItemKind::TypeAlias(def) => Ok(TyPathResolution::TypeAlias(def)),
            ItemKind::Module(_)
            | ItemKind::EnumVariant(_)
            | ItemKind::Impl(_)
            | ItemKind::Fn(_) => Ok(TyPathResolution::Other(target)),
        }
    }

    pub fn resolve_ty_item_path_as_trait(
        &self,
        path: &AstBarePath,
    ) -> Result<Obj<TraitItem>, ErrorGuaranteed> {
        let s = &self.tcx.session;

        let offending_item = match self.resolve_ty_item_path(path)? {
            TyPathResolution::Trait(def) => return Ok(def),
            TyPathResolution::GenericSig(_) | TyPathResolution::GenericHrtb(_) => {
                return Err(
                    Diag::span_err(path.span, "expected type, found generic parameter").emit(),
                );
            }
            TyPathResolution::Adt(def) => def.r(s).item,
            TyPathResolution::TypeAlias(def) => def.r(s).item,
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
    pub fn lower_ty_or_re(&mut self, ast: &AstTyOrRe) -> SigTyOrRe {
        match ast {
            AstTyOrRe::Re(ast) => SigTyOrRe::Re(self.lower_re(ast)),
            AstTyOrRe::Ty(ast) => SigTyOrRe::Ty(self.lower_ty(ast)),
        }
    }

    pub fn lower_re(&mut self, ast: &Lifetime) -> SigRe {
        if let Some(generic) = self.generic_re_names.lookup(ast.name) {
            return match *generic {
                DefinedGenericRe::Sig(generic) => SigReKind::Generic(generic).wrap(ast.span),
                DefinedGenericRe::Hrtb(_span, pos) => {
                    SigReKind::HrtbVar(HrtbDebruijn(self.generic_debruijn.make_relative(pos)))
                        .wrap(ast.span)
                }
            };
        }

        // TODO: Use actual keyword lifetimes
        if ast.name == symbol!("gc") {
            return SigReKind::Gc.wrap(ast.span);
        }

        todo!()
    }

    pub fn lower_opt_ty(&mut self, ast: Option<&AstTy>) -> Option<SigTy> {
        ast.map(|ast| self.lower_ty(ast))
    }

    pub fn lower_ty(&mut self, ast: &AstTy) -> SigTy {
        let s = &self.tcx.session;

        match &ast.kind {
            AstTyKind::This => SigTyKind::SelfTy.wrap(ast.span, s),
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

                        SigTyKind::Adt(SigAdtInstance { def, params }).wrap(ast.span, s)
                    }
                    Ok(TyPathResolution::GenericSig(def)) => {
                        SigTyKind::Generic(def).wrap(ast.span, s)
                    }
                    Ok(TyPathResolution::GenericHrtb(rel)) => {
                        SigTyKind::HrtbVar(rel).wrap(ast.span, s)
                    }
                    Ok(TyPathResolution::TypeAlias(def)) => {
                        let params = self.lower_generics_of_entirely_positional(
                            def.r(s).item,
                            def.r(s).generics,
                            ast.span,
                            generics.as_ref().map_or(&[][..], |v| &v.list),
                        );

                        SigTyKind::Alias(def, params).wrap(ast.span, s)
                    }
                    Ok(TyPathResolution::Trait(def)) => SigTyKind::Error(
                        Diag::span_err(
                            ast.span,
                            format_args!(
                                "expected a struct, enum, or type alias, found trait `{}`",
                                resolver.path(def.r(s).item),
                            ),
                        )
                        .child(LeafDiag::new(
                            Level::Help,
                            "consider prefixing the trait with `dyn`",
                        ))
                        .emit(),
                    )
                    .wrap(ast.span, s),
                    Ok(TyPathResolution::Other(def)) => SigTyKind::Error(
                        Diag::span_err(
                            ast.span,
                            format_args!(
                                "expected a struct, enum, or type alias, found {}",
                                def.r(s).bare_category_path(s),
                            ),
                        )
                        .emit(),
                    )
                    .wrap(ast.span, s),
                    Err(err) => SigTyKind::Error(err).wrap(ast.span, s),
                }
            }
            AstTyKind::Reference(lifetime, muta, pointee) => SigTyKind::Reference(
                match lifetime {
                    Some(ast) => self.lower_re(ast),
                    None => SigReKind::Infer.wrap(ast.span.shrink_to_lo()),
                },
                muta.as_muta(),
                self.lower_ty(pointee),
            )
            .wrap(ast.span, s),
            AstTyKind::Trait(lifetime, muta, spec) => SigTyKind::Trait(
                match lifetime {
                    Some(ast) => self.lower_re(ast),
                    None => SigReKind::Infer.wrap(ast.span.shrink_to_lo()),
                },
                muta.as_muta(),
                self.lower_clauses(Some(spec)),
            )
            .wrap(ast.span, s),
            AstTyKind::Paren(ast) => self.lower_ty(ast),
            AstTyKind::Tuple(items) => SigTyKind::Tuple(self.lower_tys(items)).wrap(ast.span, s),
            AstTyKind::Project(target, spec, assoc) => {
                let target = self.lower_ty(target);
                let spec = match self.lower_trait_spec(spec) {
                    Ok(spec) => spec,
                    Err(error) => return SigTyKind::Error(error).wrap(ast.span, s),
                };

                let Some(assoc_generic) = spec.def.r(s).associated_types.get(&assoc.text) else {
                    return SigTyKind::Error(
                        Diag::span_err(assoc.span, "no such associated type").emit(),
                    )
                    .wrap(ast.span, s);
                };

                SigTyKind::Project(SigProjectType {
                    target,
                    spec,
                    assoc_span: assoc.span,
                    assoc_idx: assoc_generic.r(s).binder.idx,
                })
                .wrap(ast.span, s)
            }
            AstTyKind::Infer => SigTyKind::Infer.wrap(ast.span, s),
            AstTyKind::Error(error) => SigTyKind::Error(*error).wrap(ast.span, s),
        }
    }

    pub fn lower_tys(&mut self, ast: &[AstTy]) -> SigTyList {
        let s = &self.tcx.session;

        SigTyList::new_iter(ast.iter().map(|ast| self.lower_ty(ast)), s)
    }
}

// === Trait Clause Lowering === //

impl IntraItemLowerCtxt<'_> {
    pub fn lower_clauses(&mut self, ast: Option<&AstTraitClauseList>) -> SigTraitClauseList {
        let s = &self.tcx.session;

        let Some(ast) = ast else {
            return SigTraitClauseList {
                span: Span::DUMMY,
                elems: Obj::new_slice(&[], s),
            };
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

        SigTraitClauseList {
            span: ast.span,
            elems: Obj::new_slice(&clauses, s),
        }
    }

    pub fn lower_clause(
        &mut self,
        ast: &AstTraitClause,
    ) -> Result<SigTraitClause, ErrorGuaranteed> {
        match ast {
            AstTraitClause::Outlives(AstTraitOutlivesClause { span, kind, other }) => {
                Ok(SigTraitClause {
                    span: *span,
                    kind: SigTraitClauseKind::Outlives(
                        match kind {
                            OutlivesKind::Shorter => RelationDirection::RhsOntoLhs,
                            OutlivesKind::Longer => RelationDirection::LhsOntoRhs,
                        },
                        self.lower_ty_or_re(other),
                    ),
                })
            }
            AstTraitClause::Trait(spec) => {
                let binder_params = spec.binder.as_ref().map(|v| &v.params);

                self.check_hrtb_def_ast_for_duplicates(binder_params);

                let (defs, inner) = self.scoped(|this| {
                    this.define_hrtb_defs_for_ast(binder_params);

                    (
                        this.lower_hrtb_def_clauses(binder_params),
                        this.lower_trait_spec(&spec.spec),
                    )
                });
                let inner = inner?;

                Ok(SigTraitClause {
                    span: spec.span,
                    kind: SigTraitClauseKind::Trait(SigHrtbBinder {
                        defs_span: spec.binder.as_ref().map_or(Span::DUMMY, |ast| ast.span),
                        defs,
                        inner,
                    }),
                })
            }
        }
    }

    pub fn lower_trait_spec(
        &mut self,
        ast: &AstNamedSpec,
    ) -> Result<SigTraitSpec, ErrorGuaranteed> {
        let s = &self.tcx.session;

        // Figure out which trait we're talking about.
        let def = self.resolve_ty_item_path_as_trait(&ast.path)?;

        // Lower generic parameters.
        let (positional, associated) =
            self.lower_generic_params_syntactic(ast.params.as_ref().map_or(&[][..], |v| &v.list));

        let params = self.normalize_positional_generic_arity(
            *def.r(s).generics,
            Some(*def.r(s).regular_generic_count),
            ast.span,
            &positional,
        );
        let mut params = self.construct_trait_spec_from_positionals(def, params, ast.span);

        self.lower_associated_type_generic_params(def, &mut params, &associated);

        let params = SigTraitParamList::new_slice(&params, s);

        Ok(SigTraitSpec {
            span: ast.span,
            def,
            params,
        })
    }
}
