use crate::{
    base::{
        Diag, ErrorGuaranteed, LeafDiag,
        analysis::SpannedViewEncode,
        arena::{LateInit, Obj},
        syntax::{HasSpan as _, Span},
    },
    parse::{
        ast::{
            AstGenericDef, AstGenericParamKind, AstGenericParamList, AstGenericPositional,
            AstImplLikeBody, AstImplLikeMemberKind, AstNamedSpec, AstTraitClause,
            AstTraitClauseList, AstTy, AstTyKind, AstTyOrRe,
        },
        token::Lifetime,
    },
    semantic::{
        lower::entry::{InterItemLowerCtxt, IntraItemLowerCtxt},
        syntax::{
            AnyGeneric, GenericBinder, Re, RegionGeneric, SpannedAdtInstanceView, SpannedRe,
            SpannedTraitClause, SpannedTraitClauseList, SpannedTraitClauseView,
            SpannedTraitInstance, SpannedTraitInstanceView, SpannedTraitParam,
            SpannedTraitParamList, SpannedTraitParamView, SpannedTraitSpec, SpannedTraitSpecView,
            SpannedTy, SpannedTyList, SpannedTyOrRe, SpannedTyOrReList, SpannedTyOrReView,
            SpannedTyView, TraitDef, TraitParam, TypeGeneric,
        },
    },
    utils::hash::FxHashMap,
};
use hashbrown::hash_map;
use std::cmp::Ordering;

impl<'ast> InterItemLowerCtxt<'_, 'ast> {
    pub fn lower_generic_defs(
        &mut self,
        binder: &mut GenericBinder,
        ast: &'ast AstGenericParamList,
        generic_clause_lists: &mut Vec<Option<&'ast AstTraitClauseList>>,
    ) {
        let s = &self.tcx.session;

        for def in &ast.list {
            let Some(def_kind) = def.kind.as_generic_def() else {
                Diag::span_err(def.span, "expected generic parameter definition").emit();
                continue;
            };

            match def_kind {
                AstGenericDef::Re(lifetime, clauses) => {
                    binder.defs.push(AnyGeneric::Re(Obj::new(
                        RegionGeneric {
                            span: def.span,
                            lifetime,
                            binder: LateInit::uninit(),
                            clauses: LateInit::uninit(),
                            is_synthetic: false,
                        },
                        s,
                    )));

                    generic_clause_lists.push(clauses);
                }
                AstGenericDef::Ty(ident, clauses) => {
                    binder.defs.push(AnyGeneric::Ty(Obj::new(
                        TypeGeneric {
                            span: def.span,
                            ident,
                            binder: LateInit::uninit(),
                            user_clauses: LateInit::uninit(),
                            elaborated_clauses: LateInit::uninit(),
                            is_synthetic: false,
                        },
                        s,
                    )));

                    generic_clause_lists.push(clauses);
                }
            }
        }
    }
}

impl IntraItemLowerCtxt<'_> {
    pub fn define_generics_in_binder(&mut self, binder: Obj<GenericBinder>) {
        let s = &self.tcx.session;

        for generic in &binder.r(s).defs {
            match generic {
                AnyGeneric::Re(generic) => {
                    self.generic_re_names
                        .define(generic.r(s).lifetime.name, *generic, |other| {
                            Diag::span_err(generic.r(s).span, "generic name used more than once")
                                .child(LeafDiag::span_note(
                                    other.r(s).span,
                                    "name previously used here",
                                ))
                                .emit()
                        });
                }
                AnyGeneric::Ty(generic) => {
                    self.generic_ty_names
                        .define(generic.r(s).ident.text, *generic, |other| {
                            Diag::span_err(generic.r(s).span, "generic name used more than once")
                                .child(LeafDiag::span_note(
                                    other.r(s).span,
                                    "name previously used here",
                                ))
                                .emit()
                        });
                }
            }
        }
    }

    pub fn lower_generic_def_clauses(
        &mut self,
        generics: Obj<GenericBinder>,
        clause_lists: &[Option<&AstTraitClauseList>],
    ) {
        let s = &self.tcx.session;

        for (&generic, &clause_list) in generics.r(s).defs.iter().zip(clause_lists) {
            match generic {
                AnyGeneric::Re(generic) => {
                    LateInit::init(&generic.r(s).clauses, self.lower_clauses(clause_list));
                }
                AnyGeneric::Ty(generic) => {
                    LateInit::init(&generic.r(s).user_clauses, self.lower_clauses(clause_list));
                }
            }
        }
    }

    pub fn lower_clauses(&mut self, ast: Option<&AstTraitClauseList>) -> SpannedTraitClauseList {
        let Some(ast) = ast else {
            return SpannedTraitClauseList::new_unspanned(self.tcx.intern_trait_clause_list(&[]));
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
        match ast {
            AstTraitClause::Outlives(lt) => {
                Ok(SpannedTraitClauseView::Outlives(self.lower_re(lt)).encode(lt.span, self.tcx))
            }
            AstTraitClause::Trait(spec) => {
                Ok(SpannedTraitClauseView::Trait(self.lower_trait_spec(spec)?)
                    .encode(spec.span, self.tcx))
            }
        }
    }

    pub fn lower_trait_spec(
        &mut self,
        ast: &AstNamedSpec,
    ) -> Result<SpannedTraitSpec, ErrorGuaranteed> {
        let s = &self.tcx.session;

        if let Some(path) = ast.path.as_ident()
            && self.generic_ty_names.lookup(path.text).is_some()
        {
            return Err(
                Diag::span_err(path.span, "expected a trait but got a generic type").emit(),
            );
        }

        let def = self
            .resolve_simple_path(&ast.path)?
            .r(s)
            .kind
            .as_trait()
            .ok_or_else(|| Diag::span_err(ast.path.span, "expected a trait").emit())?;

        let params = self.lower_trait_spec_generics(def, ast.span, ast.params.as_ref())?;

        Ok(SpannedTraitSpecView { def, params }.encode(ast.span, self.tcx))
    }

    pub fn lower_trait_instance(
        &mut self,
        main_ty: &AstTy,
        body: &AstImplLikeBody,
    ) -> Result<SpannedTraitInstance, ErrorGuaranteed> {
        let s = &self.tcx.session;

        // Validate path
        let AstTyKind::Name(path, generics) = &main_ty.kind else {
            return Err(Diag::span_err(main_ty.span, "expected a trait").emit());
        };

        if let Some(path) = path.as_ident()
            && self.generic_ty_names.lookup(path.text).is_some()
        {
            return Err(
                Diag::span_err(path.span, "expected a trait but got a generic type").emit(),
            );
        }

        let def = self
            .resolve_simple_path(path)?
            .r(s)
            .kind
            .as_trait()
            .ok_or_else(|| Diag::span_err(path.span, "expected a trait").emit())?;

        let mut params = Vec::new();

        // Collect positional arguments
        params.extend(
            self.lower_positional_binder_generics(
                def.r(s).generics,
                Some(def.r(s).regular_generic_count),
                main_ty.span,
                generics.as_ref(),
            )?
            .iter(self.tcx),
        );

        // Collect associated types
        let mut associated = FxHashMap::default();

        for member in &body.members {
            match &member.kind {
                AstImplLikeMemberKind::TypeEquals(name, ty_val) => {
                    let Some(generic) = def.r(s).associated_types.get(&name.text) else {
                        Diag::span_err(name.span, "no such associated type parameter").emit();
                        continue;
                    };

                    let ty_val = self.lower_ty(ty_val);

                    match associated.entry(generic) {
                        hash_map::Entry::Vacant(entry) => {
                            entry.insert((name.span, ty_val));
                        }
                        hash_map::Entry::Occupied(entry) => {
                            Diag::span_err(name.span, "associated type specified more than once")
                                .child(LeafDiag::span_note(
                                    entry.get().0,
                                    "type first specified here",
                                ))
                                .emit();

                            continue;
                        }
                    }
                }
                AstImplLikeMemberKind::TypeInherits(..) => {
                    Diag::span_err(member.span, "associated type in `impl` without body").emit();
                }
                AstImplLikeMemberKind::Func(..) => {
                    todo!();
                }
                AstImplLikeMemberKind::Error(_) => {
                    // (ignored)
                }
            }
        }

        for generic in &def.r(s).generics.r(s).defs[(def.r(s).regular_generic_count as usize)..] {
            let generic = generic.unwrap_ty();

            let Some((_, assoc)) = associated.get(&generic) else {
                return Err(Diag::span_err(
                    path.span,
                    format_args!("missing associated type `{}`", generic.r(s).ident.text),
                )
                .emit());
            };

            params.push(SpannedTyOrReView::Ty(*assoc).encode(generic.r(s).span, self.tcx));
        }

        Ok(SpannedTraitInstanceView {
            def,
            params: SpannedTyOrReList::alloc_list(main_ty.span, &params, self.tcx),
        }
        .encode(main_ty.span, self.tcx))
    }

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
            return Re::Universal(*generic).encode(ast.span, self.tcx);
        }

        todo!()
    }

    pub fn lower_opt_ty(&mut self, ast: Option<&AstTy>) -> Option<SpannedTy> {
        ast.map(|ast| self.lower_ty(ast))
    }

    pub fn lower_ty(&mut self, ast: &AstTy) -> SpannedTy {
        let s = &self.tcx.session;

        match &ast.kind {
            AstTyKind::This => SpannedTyView::This.encode(ast.span, self.tcx),
            AstTyKind::Name(path, generics) => {
                if let Some(name) = path.parts[0].ident()
                    && let Some(generic) = self.generic_ty_names.lookup(name.text)
                {
                    if let Some(subsequent) = path.parts.get(1) {
                        Diag::span_err(
                            subsequent.span(),
                            "generic types cannot be accessed like modules",
                        )
                        .emit();
                    } else if let Some(generics) = generics {
                        Diag::span_err(
                            generics.span,
                            "generic types cannot be instantiated with further generic parameters",
                        )
                        .emit();
                    }

                    return SpannedTyView::Universal(*generic).encode(ast.span, self.tcx);
                }

                let def = match self.resolve_simple_path(path) {
                    Ok(def) => def,
                    Err(err) => {
                        return SpannedTyView::Error(err).encode(ast.span, self.tcx);
                    }
                };

                let Some(def) = def.r(s).kind.as_adt() else {
                    return SpannedTyView::Error(
                        Diag::span_err(path.span, "expected enum or struct").emit(),
                    )
                    .encode(ast.span, self.tcx);
                };

                let params = match self.lower_positional_binder_generics(
                    def.r(s).generics,
                    None,
                    ast.span,
                    generics.as_ref(),
                ) {
                    Ok(v) => v,
                    Err(err) => {
                        return SpannedTyView::Error(err).encode(ast.span, self.tcx);
                    }
                };

                SpannedTyView::Adt(
                    SpannedAdtInstanceView { def, params }.encode(ast.span, self.tcx),
                )
                .encode(ast.span, self.tcx)
            }
            AstTyKind::Reference(lifetime, muta, pointee) => SpannedTyView::Reference(
                match lifetime {
                    Some(ast) => self.lower_re(ast),
                    None => Re::ExplicitInfer.encode(ast.span.shrink_to_lo(), self.tcx),
                },
                muta.as_muta(),
                self.lower_ty(pointee),
            )
            .encode(ast.span, self.tcx),
            AstTyKind::Trait(spec) => {
                SpannedTyView::Trait(self.lower_clauses(Some(spec))).encode(ast.span, self.tcx)
            }
            AstTyKind::Tuple(items) => {
                SpannedTyView::Tuple(self.lower_tys(items)).encode(ast.span, self.tcx)
            }
            AstTyKind::Infer => SpannedTyView::ExplicitInfer.encode(ast.span, self.tcx),
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

    pub fn lower_trait_spec_generics(
        &mut self,
        def: Obj<TraitDef>,
        segment_span: Span,
        ast: Option<&AstGenericParamList>,
    ) -> Result<SpannedTraitParamList, ErrorGuaranteed> {
        let s = &self.tcx.session;

        let mut reader = ast.as_ref().map_or(&[][..], |v| &v.list).iter();
        let mut params = Vec::new();

        // Lower positional arguments
        if reader.len() < def.r(s).regular_generic_count as usize {
            return Err(Diag::span_err(segment_span, "missing generic parameters").emit());
        }

        for (param, generic) in (&mut reader)
            .zip(&def.r(s).generics.r(s).defs)
            .take(def.r(s).regular_generic_count as usize)
        {
            match &param.kind {
                AstGenericParamKind::PositionalTy(ty) => {
                    if !matches!(generic, AnyGeneric::Ty(_)) {
                        return Err(Diag::span_err(ty.span, "expected lifetime parameter").emit());
                    }

                    params.push(
                        SpannedTraitParamView::Equals(
                            SpannedTyOrReView::Ty(self.lower_ty(ty)).encode(ty.span, self.tcx),
                        )
                        .encode(param.span, self.tcx),
                    );
                }
                AstGenericParamKind::PositionalRe(re) => {
                    if !matches!(generic, AnyGeneric::Re(_)) {
                        return Err(Diag::span_err(re.span, "expected type parameter").emit());
                    }

                    params.push(
                        SpannedTraitParamView::Equals(
                            SpannedTyOrReView::Re(self.lower_re(re)).encode(re.span, self.tcx),
                        )
                        .encode(re.span, self.tcx),
                    );
                }
                AstGenericParamKind::InheritRe(..) => {
                    Diag::span_err(param.span, "cannot name lifetime parameters").emit();
                    continue;
                }
                AstGenericParamKind::TyEquals(..) | AstGenericParamKind::InheritTy(..) => {
                    return Err(Diag::span_err(segment_span, "missing generic parameters").emit());
                }
            }
        }

        // Lower trait clauses
        params.resize_with(def.r(s).generics.r(s).defs.len(), || {
            SpannedTraitParam::new_unspanned(TraitParam::Unspecified(
                self.tcx.intern_trait_clause_list(&[]),
            ))
        });

        for param in &mut reader {
            let name = match &param.kind {
                AstGenericParamKind::TyEquals(name, _) => name,
                AstGenericParamKind::InheritTy(name, _) => name,
                AstGenericParamKind::PositionalTy(..) | AstGenericParamKind::PositionalRe(..) => {
                    return Err(Diag::span_err(param.span, "too many generic parameters").emit());
                }
                AstGenericParamKind::InheritRe(..) => {
                    Diag::span_err(param.span, "cannot name lifetime parameters").emit();
                    continue;
                }
            };

            let Some(generic) = def.r(s).associated_types.get(&name.text) else {
                return Err(Diag::span_err(
                    name.span,
                    "trait does not have associated type with that name",
                )
                .emit());
            };

            let idx = generic.r(s).binder.unwrap().idx as usize;

            match params[idx].value {
                TraitParam::Unspecified(list) if list.r(s).is_empty() => {
                    // (fallthrough)
                }
                _ => {
                    return Err(Diag::span_err(
                        param.span,
                        "associated type mentioned more than once",
                    )
                    .emit());
                }
            }

            params[idx] = match &param.kind {
                AstGenericParamKind::TyEquals(_, ast) => SpannedTraitParamView::Equals(
                    SpannedTyOrReView::Ty(self.lower_ty(ast)).encode(ast.span, self.tcx),
                )
                .encode(param.span, self.tcx),
                AstGenericParamKind::InheritTy(_, ast) => {
                    SpannedTraitParamView::Unspecified(self.lower_clauses(Some(ast)))
                        .encode(param.span, self.tcx)
                }
                AstGenericParamKind::PositionalTy(..)
                | AstGenericParamKind::PositionalRe(..)
                | AstGenericParamKind::InheritRe(..) => unreachable!(),
            };
        }

        Ok(SpannedTraitParamList::alloc_list(
            segment_span,
            &params,
            self.tcx,
        ))
    }

    pub fn lower_positional_binder_generics(
        &mut self,
        binder: Obj<GenericBinder>,
        binder_len_override: Option<u32>,
        segment_span: Span,
        ast: Option<&AstGenericParamList>,
    ) -> Result<SpannedTyOrReList, ErrorGuaranteed> {
        let s = &self.tcx.session;

        let binder_len = binder_len_override.map_or(binder.r(s).defs.len(), |v| v as usize);
        let ast = ast.as_ref().map_or(&[][..], |v| v.list.as_slice());

        let mut had_error = None;

        match ast.len().cmp(&binder_len) {
            Ordering::Equal => {
                // (fallthrough)
            }
            Ordering::Less => {
                had_error = Some(Diag::span_err(segment_span, "missing generic parameters").emit());
            }
            Ordering::Greater => {
                had_error = Some(
                    Diag::span_err(ast[binder_len].span, "too many generic parameters").emit(),
                );
            }
        }

        let mut params = Vec::new();

        for (actual, expected) in ast.iter().zip(&binder.r(s).defs[..binder_len]) {
            let actual_span = actual.span;

            let Some(actual) = actual.kind.as_positional() else {
                had_error = Some(
                    Diag::span_err(actual.span, "expected a positional generic parameter").emit(),
                );

                continue;
            };

            match (actual, expected) {
                (AstGenericPositional::Ty(actual), AnyGeneric::Ty(_)) => {
                    params.push(
                        SpannedTyOrReView::Ty(self.lower_ty(actual)).encode(actual_span, self.tcx),
                    );
                }
                (AstGenericPositional::Re(actual), AnyGeneric::Re(_)) => {
                    params.push(
                        SpannedTyOrReView::Re(self.lower_re(actual)).encode(actual_span, self.tcx),
                    );
                }
                (_, AnyGeneric::Ty(_)) => {
                    had_error = Some(Diag::span_err(actual_span, "expected a type").emit());
                }
                (_, AnyGeneric::Re(_)) => {
                    had_error = Some(Diag::span_err(actual_span, "expected a lifetime").emit());
                }
            }
        }

        if let Some(err) = had_error {
            return Err(err);
        }

        Ok(SpannedTyOrReList::alloc_list(
            segment_span,
            &params,
            self.tcx,
        ))
    }
}
