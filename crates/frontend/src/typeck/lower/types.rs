use crate::{
    base::{Diag, ErrorGuaranteed, LeafDiag, arena::Obj},
    parse::{
        ast::{
            AstGenericParamKind, AstImplLikeBody, AstImplLikeMemberKind, AstNamedSpec,
            AstTraitClause, AstTraitClauseList, AstTy, AstTyKind, AstTyOrRe,
        },
        token::Lifetime,
    },
    typeck::{
        lower::entry::IntraItemLowerCtxt,
        syntax::{
            AnyGeneric, GenericBinder, Re, TraitClause, TraitClauseList, TraitInstance, TraitParam,
            TraitSpec, Ty, TyKind, TyList, TyOrRe,
        },
    },
    utils::hash::FxHashMap,
};
use hashbrown::hash_map;

impl IntraItemLowerCtxt<'_> {
    pub fn define_generics_in_binder(&mut self, binder: Obj<GenericBinder>) {
        let s = &self.tcx.session;

        for generic in &binder.r(s).generics {
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

    pub fn lower_clauses(&mut self, ast: Option<&AstTraitClauseList>) -> TraitClauseList {
        let Some(ast) = ast else {
            return self.tcx.intern_trait_clause_list(&[]);
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

        self.tcx.intern_trait_clause_list(&clauses)
    }

    pub fn lower_clause(&mut self, ast: &AstTraitClause) -> Result<TraitClause, ErrorGuaranteed> {
        match ast {
            AstTraitClause::Outlives(lt) => Ok(TraitClause::Outlives(self.lower_re(lt))),
            AstTraitClause::Trait(spec) => Ok(TraitClause::Trait(self.lower_trait_spec(spec)?)),
        }
    }

    pub fn lower_trait_spec(&mut self, ast: &AstNamedSpec) -> Result<TraitSpec, ErrorGuaranteed> {
        let s = &self.tcx.session;

        if let Some(path) = ast.path.as_ident()
            && self.generic_ty_names.lookup(path.text).is_some()
        {
            return Err(
                Diag::span_err(path.span, "expected a trait but got a generic type").emit(),
            );
        }

        let def = self
            .lookup(&ast.path)?
            .as_item()
            .and_then(|v| v.r(s).kind.as_trait())
            .ok_or_else(|| Diag::span_err(ast.path.span, "expected a trait").emit())?;

        let mut params = Vec::new();
        let mut reader = ast.params.as_ref().map_or(&[][..], |v| &v.list).iter();

        // Lower positional arguments
        if reader.len() < def.r(s).regular_generic_count as usize {
            return Err(Diag::span_err(ast.span, "missing generic parameters").emit());
        }

        for (param, generic) in (&mut reader)
            .zip(&def.r(s).generics.r(s).generics)
            .take(def.r(s).regular_generic_count as usize)
        {
            match &param.kind {
                AstGenericParamKind::PositionalTy(ty) => {
                    if !matches!(generic, AnyGeneric::Ty(_)) {
                        return Err(Diag::span_err(ty.span, "expected lifetime parameter").emit());
                    }

                    params.push(TraitParam::Equals(TyOrRe::Ty(self.lower_ty(ty))));
                }
                AstGenericParamKind::PositionalRe(ty) => {
                    if !matches!(generic, AnyGeneric::Re(_)) {
                        return Err(Diag::span_err(ty.span, "expected type parameter").emit());
                    }

                    params.push(TraitParam::Equals(TyOrRe::Re(self.lower_re(ty))));
                }
                AstGenericParamKind::InheritRe(..) => {
                    Diag::span_err(param.span, "cannot name lifetime parameters").emit();
                    continue;
                }
                AstGenericParamKind::TyEquals(..) | AstGenericParamKind::InheritTy(..) => {
                    return Err(Diag::span_err(ast.span, "missing generic parameters").emit());
                }
            }
        }

        // Lower trait clauses
        params.resize_with(def.r(s).generics.r(s).generics.len(), || {
            TraitParam::Unspecified(self.tcx.intern_trait_clause_list(&[]))
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

            let idx = generic.r(s).binder.idx as usize;

            match params[idx] {
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
                AstGenericParamKind::TyEquals(_, ast) => {
                    TraitParam::Equals(TyOrRe::Ty(self.lower_ty(ast)))
                }
                AstGenericParamKind::InheritTy(_, ast) => {
                    TraitParam::Unspecified(self.lower_clauses(Some(ast)))
                }
                AstGenericParamKind::PositionalTy(..)
                | AstGenericParamKind::PositionalRe(..)
                | AstGenericParamKind::InheritRe(..) => unreachable!(),
            };
        }

        Ok(TraitSpec {
            def,
            params: self.tcx.intern_trait_param_list(&params),
        })
    }

    pub fn lower_trait_instance(
        &mut self,
        main_ty: &AstTy,
        body: &AstImplLikeBody,
    ) -> Result<TraitInstance, ErrorGuaranteed> {
        let s = &self.tcx.session;

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
            .lookup(path)?
            .as_item()
            .and_then(|v| v.r(s).kind.as_trait())
            .ok_or_else(|| Diag::span_err(path.span, "expected a trait").emit())?;

        let mut params = Vec::new();
        let generics = generics.as_ref().map_or(&[][..], |v| &v.list);

        // Ensure that no generics are associated types
        for generic in generics {
            match &generic.kind {
                AstGenericParamKind::PositionalTy(..) | AstGenericParamKind::PositionalRe(..) => {
                    // (no-op)
                }
                AstGenericParamKind::InheritRe(..) => {
                    Diag::span_err(generic.span, "cannot name lifetime parameters").emit();
                    continue;
                }
                AstGenericParamKind::TyEquals(..) | AstGenericParamKind::InheritTy(..) => {
                    return Err(Diag::span_err(
                        generic.span,
                        "associated types must be specified in the `impl` block body",
                    )
                    .emit());
                }
            }
        }

        // Lower positional arguments
        if generics.len() < def.r(s).regular_generic_count as usize {
            return Err(Diag::span_err(main_ty.span, "missing generic parameters").emit());
        }

        if generics.len() > def.r(s).regular_generic_count as usize {
            return Err(Diag::span_err(
                generics[def.r(s).regular_generic_count as usize].span,
                "too many generic parameters",
            )
            .emit());
        }

        for (param, generic) in generics.iter().zip(&def.r(s).generics.r(s).generics) {
            match &param.kind {
                AstGenericParamKind::PositionalTy(ty) => {
                    if !matches!(generic, AnyGeneric::Ty(_)) {
                        return Err(Diag::span_err(ty.span, "expected lifetime parameter").emit());
                    }

                    params.push(TyOrRe::Ty(self.lower_ty(ty)));
                }
                AstGenericParamKind::PositionalRe(ty) => {
                    if !matches!(generic, AnyGeneric::Re(_)) {
                        return Err(Diag::span_err(ty.span, "expected type parameter").emit());
                    }

                    params.push(TyOrRe::Re(self.lower_re(ty)));
                }
                AstGenericParamKind::InheritRe(..)
                | AstGenericParamKind::TyEquals(..)
                | AstGenericParamKind::InheritTy(..) => {
                    unreachable!()
                }
            }
        }

        // Lower associated types.
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
                AstImplLikeMemberKind::Error(_) => {
                    // (ignored)
                }
            }
        }

        for generic in &def.r(s).generics.r(s).generics[(def.r(s).regular_generic_count as usize)..]
        {
            let generic = generic.unwrap_ty();

            let Some((_, assoc)) = associated.get(&generic) else {
                return Err(Diag::span_err(
                    path.span,
                    format_args!("missing associated type `{}`", generic.r(s).ident.text),
                )
                .emit());
            };

            params.push(TyOrRe::Ty(*assoc));
        }

        Ok(TraitInstance {
            def,
            params: self.tcx.intern_ty_or_re_list(&params),
        })
    }

    pub fn lower_ty_or_re(&mut self, ast: &AstTyOrRe) -> TyOrRe {
        match ast {
            AstTyOrRe::Re(ast) => TyOrRe::Re(self.lower_re(ast)),
            AstTyOrRe::Ty(ast) => TyOrRe::Ty(self.lower_ty(ast)),
        }
    }

    pub fn lower_re(&mut self, ast: &Lifetime) -> Re {
        if let Some(generic) = self.generic_re_names.lookup(ast.name) {
            return Re::Generic(*generic);
        }

        todo!()
    }

    pub fn lower_ty(&mut self, ast: &AstTy) -> Ty {
        match &ast.kind {
            AstTyKind::This => self.tcx.intern_ty(TyKind::This),
            AstTyKind::Name(path, generics) => {
                if let Some(generic) = self.generic_ty_names.lookup(path.parts[0].text) {
                    if let Some(subsequent) = path.parts.get(1) {
                        Diag::span_err(
                            subsequent.span,
                            "generic types cannot be accessed like modules",
                        )
                        .emit();
                    } else if let Some(generics) = generics
                        && let Some(para) = generics.list.first()
                    {
                        Diag::span_err(
                            para.span,
                            "generic types cannot be instantiated with further generic parameters",
                        )
                        .emit();
                    }

                    return self.tcx.intern_ty(TyKind::Universal(*generic));
                }

                todo!()
            }
            AstTyKind::Reference(lifetime, pointee) => self.tcx.intern_ty(TyKind::Reference(
                lifetime.map_or(Re::ExplicitInfer, |ast| self.lower_re(&ast)),
                self.lower_ty(pointee),
            )),
            AstTyKind::Trait(spec) => self
                .tcx
                .intern_ty(TyKind::Trait(self.lower_clauses(Some(spec)))),
            AstTyKind::Tuple(items) => self.tcx.intern_ty(TyKind::Tuple(self.lower_tys(items))),
            AstTyKind::Option(item) => todo!(),
            AstTyKind::Infer => self.tcx.intern_ty(TyKind::ExplicitInfer),
            AstTyKind::Error(error) => self.tcx.intern_ty(TyKind::Error(*error)),
        }
    }

    pub fn lower_tys(&mut self, ast: &[AstTy]) -> TyList {
        self.tcx
            .intern_tys(&ast.iter().map(|ast| self.lower_ty(ast)).collect::<Vec<_>>())
    }
}
