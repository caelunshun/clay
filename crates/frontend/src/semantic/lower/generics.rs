use crate::{
    base::{
        Diag, ErrorGuaranteed, LeafDiag, Level,
        analysis::SpannedViewEncode as _,
        arena::{LateInit, Obj},
        syntax::{Span, Symbol},
    },
    parse::{
        ast::{
            AstGenericDef, AstGenericParam, AstGenericParamKind, AstGenericParamList,
            AstImplLikeBody, AstImplLikeMemberKind, AstTraitClauseList, AstTy, AstTyKind,
        },
        token::Ident,
    },
    semantic::{
        lower::{
            entry::{InterItemLowerCtxt, IntraItemLowerCtxt},
            modules::{FrozenModuleResolver, ParentResolver as _, PathResolver as _},
        },
        syntax::{
            AdtDef, AnyGeneric, GenericBinder, Re, RegionGeneric, SpannedTraitClauseList,
            SpannedTraitInstance, SpannedTraitInstanceView, SpannedTraitParam,
            SpannedTraitParamView, SpannedTyOrRe, SpannedTyOrReList, SpannedTyOrReView,
            SpannedTyView, TraitDef, TypeGeneric,
        },
    },
    utils::{
        hash::FxHashMap,
        lang::{AND_LIST_GLUE, format_list},
    },
};
use hashbrown::hash_map;
use std::iter;

// === Generic definition lowering === //

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
}

// === Complete generic lowering routines === //

impl IntraItemLowerCtxt<'_> {
    pub fn lower_type_relative_generics(
        &mut self,
        args: Option<&AstGenericParamList>,
    ) -> Option<SpannedTyOrReList> {
        args.as_ref().map(|args| {
            let (positional, associated) = self.lower_generic_params_syntactic(&args.list);

            if let Some(associated) = associated.first() {
                Diag::span_err(
                    associated.span,
                    "method or constant does not have associated type constraints",
                )
                .emit();
            }

            SpannedTyOrReList::alloc_list(args.span, &positional, self.tcx)
        })
    }

    pub fn lower_generics_of_adt(
        &mut self,
        def: Obj<AdtDef>,
        segment_span: Span,
        generics: &[AstGenericParam],
    ) -> SpannedTyOrReList {
        let s = &self.tcx.session;

        let (positional, associated) = self.lower_generic_params_syntactic(generics);

        let params = self.normalize_positional_generic_arity(
            def.r(s).generics,
            None,
            segment_span,
            &positional,
        );

        if let Some(associated) = associated.first() {
            let resolver = FrozenModuleResolver(s);

            Diag::span_err(
                associated.span,
                format_args!(
                    "{} `{}` does not have any associated type constraints",
                    resolver.categorize(def.r(s).item).bare_what(),
                    resolver.path(def.r(s).item),
                ),
            )
            .emit();
        }

        params
    }

    pub fn lower_generics_of_trait_instance(
        &mut self,
        def: Obj<TraitDef>,
        segment_span: Span,
        generics: Option<&AstGenericParamList>,
    ) -> SpannedTyOrReList {
        let s = &self.tcx.session;

        let Some(generics) = generics else {
            return self.construct_trait_instance_from_positionals(
                def,
                self.synthesize_inferred_generics_for_elision(
                    def.r(s).generics,
                    None,
                    segment_span,
                ),
                segment_span,
            );
        };

        let (positional, associated) = self.lower_generic_params_syntactic(&generics.list);

        let params = self.normalize_positional_generic_arity(
            def.r(s).generics,
            None,
            segment_span,
            &positional,
        );

        if let Some(associated) = associated.first() {
            Diag::span_err(associated.span, "associated types cannot be specified here").emit();
        }

        self.construct_trait_instance_from_positionals(def, params, segment_span)
    }

    pub fn lower_trait_instance_of_impl_block(
        &mut self,
        for_trait: &AstTy,
        body: &AstImplLikeBody,
    ) -> Result<SpannedTraitInstance, ErrorGuaranteed> {
        let s = &self.tcx.session;

        // Lower target item.
        let AstTyKind::Name(for_trait_path, for_trait_generics) = &for_trait.kind else {
            return Err(Diag::span_err(for_trait.span, "expected a trait, found a type").emit());
        };

        let def = self.resolve_ty_item_path_as_trait(for_trait_path)?;

        // Lower positional parameters.
        let (positional, associated) = self.lower_generic_params_syntactic(
            for_trait_generics.as_ref().map_or(&[][..], |v| &v.list),
        );

        let params = self.normalize_positional_generic_arity(
            def.r(s).generics,
            Some(def.r(s).regular_generic_count),
            for_trait.span,
            &positional,
        );

        if let Some(first) = associated.first() {
            Diag::span_err(
                first.span,
                "associated types must be specified in the `impl` block body",
            )
            .emit();
        }

        // Lower trait members
        let mut params = params
            .iter(self.tcx)
            .map(Some)
            .chain(iter::repeat(None))
            .take(def.r(s).generics.r(s).defs.len())
            .collect::<Vec<_>>();

        for member in &body.members {
            match &member.kind {
                AstImplLikeMemberKind::TypeEquals(name, exact_ty) => {
                    let Some(generic) = def.r(s).associated_types.get(&name.text) else {
                        Diag::span_err(name.span, "no such associated type parameter").emit();
                        continue;
                    };

                    let exact_ty = self.lower_ty(exact_ty);

                    let param = &mut params[generic.r(s).binder.unwrap().idx as usize];

                    if let Some(old_param) = param {
                        Diag::span_err(name.span, "associated type specified more than once")
                            .child(LeafDiag::span_note(
                                old_param.own_span().unwrap_or(Span::DUMMY),
                                "type first specified here",
                            ))
                            .emit();
                    } else {
                        *param = Some(
                            SpannedTyOrReView::Ty(exact_ty)
                                .encode(exact_ty.own_span().unwrap_or(Span::DUMMY), self.tcx),
                        );
                    }
                }
                AstImplLikeMemberKind::TypeInherits(..)
                | AstImplLikeMemberKind::Func(..)
                | AstImplLikeMemberKind::Error(_) => {
                    // (ignored)
                }
            }
        }

        // Ensure that all parameters are present.
        let missing_mentions = params
            .iter()
            .zip(&def.r(s).generics.r(s).defs)
            .filter_map(|(supplied, expected)| {
                if supplied.is_some() {
                    return None;
                }

                Some(expected.as_ty().unwrap().r(s).ident.text)
            })
            .collect::<Vec<_>>();

        let missing_mentions = (!missing_mentions.is_empty()).then(|| {
            Diag::span_err(
                for_trait.span,
                format_args!(
                    "missing associated types {}",
                    format_list(
                        missing_mentions.iter().map(|v| format!("`{v}`")),
                        AND_LIST_GLUE
                    )
                ),
            )
            .emit()
        });

        let params = params
            .iter()
            .map(|param| {
                param.unwrap_or_else(|| {
                    SpannedTyOrReView::Ty(
                        SpannedTyView::Error(missing_mentions.unwrap())
                            .encode(for_trait.span, self.tcx),
                    )
                    .encode(for_trait.span, self.tcx)
                })
            })
            .collect::<Vec<_>>();

        let params = SpannedTyOrReList::alloc_list(for_trait.span, &params, self.tcx);

        Ok(SpannedTraitInstanceView { def, params }.encode(for_trait.span, self.tcx))
    }
}

// === Generic parameter lowering helpers === //

#[derive(Debug, Copy, Clone)]
pub struct LoweredAssocConstraint {
    pub span: Span,
    pub name: Ident,
    pub param: SpannedTraitParam,
}

impl IntraItemLowerCtxt<'_> {
    pub fn lower_generic_params_syntactic(
        &mut self,
        params: &[AstGenericParam],
    ) -> (Vec<SpannedTyOrRe>, Vec<LoweredAssocConstraint>) {
        let mut positional = Vec::<SpannedTyOrRe>::new();
        let mut associated = Vec::<LoweredAssocConstraint>::new();

        let mut printed_ordering_err = false;
        let mut check_ordering = |positional_span: Span, associated: &[LoweredAssocConstraint]| {
            if !printed_ordering_err && let Some(associated) = associated.first() {
                Diag::anon_err("generic arguments must come before the first constraint")
                    .primary(positional_span, "generic argument")
                    .primary(associated.span, "constraint")
                    .emit();

                printed_ordering_err = true;
            }
        };

        let mut mentioned_associations = FxHashMap::<Symbol, Span>::default();
        let mut check_mention = |name: Ident| -> bool {
            match mentioned_associations.entry(name.text) {
                hash_map::Entry::Vacant(entry) => {
                    entry.insert(name.span);
                    true
                }
                hash_map::Entry::Occupied(entry) => {
                    Diag::anon_err("associated constraint specified more than once")
                        .primary(name.span, "redundant specification")
                        .secondary(*entry.get(), "first specification")
                        .emit();
                    false
                }
            }
        };

        for ast_param in params {
            match &ast_param.kind {
                AstGenericParamKind::PositionalTy(ty) => {
                    check_ordering(ty.span, &associated);

                    positional
                        .push(SpannedTyOrReView::Ty(self.lower_ty(ty)).encode(ty.span, self.tcx));
                }
                AstGenericParamKind::PositionalRe(re) => {
                    check_ordering(re.span, &associated);

                    positional
                        .push(SpannedTyOrReView::Re(self.lower_re(re)).encode(re.span, self.tcx));
                }
                AstGenericParamKind::InheritTy(name, clauses) => {
                    let param =
                        SpannedTraitParamView::Unspecified(self.lower_clauses(Some(clauses)))
                            .encode(clauses.span, self.tcx);

                    if check_mention(*name) {
                        associated.push(LoweredAssocConstraint {
                            span: ast_param.span,
                            name: *name,
                            param,
                        });
                    }
                }
                AstGenericParamKind::TyEquals(name, equals) => {
                    let param = SpannedTraitParamView::Equals(
                        SpannedTyOrReView::Ty(self.lower_ty(equals)).encode(equals.span, self.tcx),
                    )
                    .encode(equals.span, self.tcx);

                    if check_mention(*name) {
                        associated.push(LoweredAssocConstraint {
                            span: ast_param.span,
                            name: *name,
                            param,
                        });
                    }
                }
                AstGenericParamKind::InheritRe(_, _) => {
                    Diag::span_err(
                        ast_param.span,
                        "existential generic constraints are not supported",
                    )
                    .emit();
                }
            }
        }

        (positional, associated)
    }

    pub fn normalize_positional_generic_arity(
        &mut self,
        binder: Obj<GenericBinder>,
        binder_len_override: Option<u32>,
        segment_span: Span,
        params: &[SpannedTyOrRe],
    ) -> SpannedTyOrReList {
        let s = &self.tcx.session;

        let binder_len = binder_len_override.map_or(binder.r(s).defs.len(), |v| v as usize);

        let mut errored_out_missing = None;

        let params = binder.r(s).defs[..binder_len]
            .iter()
            .zip(params.iter().map(Some).chain(iter::repeat(None)))
            .map(|(expected, actual)| {
                let actual_span =
                    actual.map_or(segment_span, |v| v.own_span().unwrap_or(segment_span));

                let para_or_err = 'para_or_err: {
                    let Some(&actual) = actual else {
                        break 'para_or_err Err(*errored_out_missing.get_or_insert_with(|| {
                            Diag::span_err(segment_span, "missing generic parameters")
                                .child(LeafDiag::new(
                                    Level::Note,
                                    format_args!(
                                        "expected {} generic parameter{} but got {}",
                                        binder_len,
                                        if binder_len == 1 { "" } else { "s" },
                                        params.len(),
                                    ),
                                ))
                                .emit()
                        }));
                    };

                    match (actual.view(self.tcx), expected) {
                        (SpannedTyOrReView::Ty(_), AnyGeneric::Ty(_)) => Ok(actual),
                        (SpannedTyOrReView::Re(_), AnyGeneric::Re(_)) => Ok(actual),
                        (_, AnyGeneric::Ty(_)) => Err(Diag::span_err(
                            actual_span,
                            "expected a type but got a lifetime",
                        )
                        .emit()),
                        (_, AnyGeneric::Re(_)) => Err(Diag::span_err(
                            actual_span,
                            "expected a lifetime but got a type",
                        )
                        .emit()),
                    }
                };

                para_or_err.unwrap_or_else(|err| match expected {
                    AnyGeneric::Re(_) => {
                        SpannedTyOrReView::Re(Re::Error(err).encode(actual_span, self.tcx))
                            .encode(actual_span, self.tcx)
                    }
                    AnyGeneric::Ty(_) => SpannedTyOrReView::Ty(
                        SpannedTyView::Error(err).encode(actual_span, self.tcx),
                    )
                    .encode(actual_span, self.tcx),
                })
            })
            .collect::<Vec<_>>();

        if params.len() > binder_len {
            Diag::span_err(
                params[binder_len].own_span().unwrap_or(Span::DUMMY),
                "too many generic parameters",
            )
            .child(LeafDiag::new(
                Level::Note,
                format_args!(
                    "expected {} generic parameter{} but got {}",
                    binder_len,
                    if binder_len == 1 { "" } else { "s" },
                    params.len(),
                ),
            ))
            .emit();
        }

        SpannedTyOrReList::alloc_list(segment_span, &params, self.tcx)
    }

    pub fn synthesize_inferred_generics_for_elision(
        &self,
        binder: Obj<GenericBinder>,
        binder_len_override: Option<u32>,
        segment_span: Span,
    ) -> SpannedTyOrReList {
        let s = &self.tcx.session;

        let binder_len = binder_len_override.map_or(binder.r(s).defs.len(), |v| v as usize);

        let params = binder.r(s).defs[..binder_len]
            .iter()
            .map(|expected| match expected {
                AnyGeneric::Re(_) => {
                    SpannedTyOrReView::Re(Re::ExplicitInfer.encode(segment_span, self.tcx))
                        .encode(segment_span, self.tcx)
                }
                AnyGeneric::Ty(_) => SpannedTyOrReView::Ty(
                    SpannedTyView::ExplicitInfer.encode(segment_span, self.tcx),
                )
                .encode(segment_span, self.tcx),
            })
            .collect::<Vec<_>>();

        SpannedTyOrReList::alloc_list(segment_span, &params, self.tcx)
    }

    pub fn construct_trait_spec_from_positionals(
        &mut self,
        def: Obj<TraitDef>,
        params: SpannedTyOrReList,
        outer_span: Span,
    ) -> Vec<SpannedTraitParam> {
        let s = &self.tcx.session;

        debug_assert_eq!(def.r(s).regular_generic_count as usize, params.len(s));

        params
            .iter(self.tcx)
            .map(|ty_or_re| {
                SpannedTraitParamView::Equals(ty_or_re)
                    .encode(ty_or_re.own_span().unwrap_or(Span::DUMMY), self.tcx)
            })
            .chain(iter::repeat(
                SpannedTraitParamView::Unspecified(SpannedTraitClauseList::alloc_list(
                    outer_span,
                    &[],
                    self.tcx,
                ))
                .encode(outer_span, self.tcx),
            ))
            .take(def.r(s).generics.r(s).defs.len())
            .collect::<Vec<_>>()
    }

    pub fn construct_trait_instance_from_positionals(
        &mut self,
        def: Obj<TraitDef>,
        params: SpannedTyOrReList,
        outer_span: Span,
    ) -> SpannedTyOrReList {
        let s = &self.tcx.session;

        debug_assert_eq!(def.r(s).regular_generic_count as usize, params.len(s));

        let elaborated_params = params
            .iter(self.tcx)
            .chain(iter::repeat(
                SpannedTyOrReView::Ty(SpannedTyView::ExplicitInfer.encode(outer_span, self.tcx))
                    .encode(outer_span, self.tcx),
            ))
            .take(def.r(s).generics.r(s).defs.len())
            .collect::<Vec<_>>();

        SpannedTyOrReList::alloc_list(
            params.own_span().unwrap_or(Span::DUMMY),
            &elaborated_params,
            self.tcx,
        )
    }

    pub fn lower_associated_type_generic_params(
        &mut self,
        def: Obj<TraitDef>,
        params: &mut [SpannedTraitParam],
        associated: &[LoweredAssocConstraint],
    ) {
        let s = &self.tcx.session;
        let resolver = FrozenModuleResolver(s);

        for associated in associated {
            let Some(generic) = def.r(s).associated_types.get(&associated.name.text) else {
                Diag::span_err(
                    associated.name.span,
                    format_args!(
                        "{} `{}` does not have associated type `{}`",
                        resolver.categorize(def.r(s).item).bare_what(),
                        resolver.path(def.r(s).item),
                        associated.name.text,
                    ),
                )
                .emit();

                continue;
            };

            let idx = generic.r(s).binder.unwrap().idx as usize;

            params[idx] = associated.param;
        }
    }
}
