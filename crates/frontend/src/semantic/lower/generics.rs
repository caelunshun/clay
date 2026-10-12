use crate::{
    base::{
        Diag, ErrorGuaranteed, LeafDiag, Level, Session,
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
        lower::entry::{
            DefinedGenericRe, DefinedGenericTy, InterItemLowerCtxt, IntraItemLowerCtxt,
        },
        syntax::{
            AnyGeneric, AnyGenericIdent, GenericBinder, Item, RegionGeneric, SigGenericList,
            SigHrtbDebruijnDef, SigHrtbDebruijnDefList, SigReKind, SigTraitClauseList,
            SigTraitInstance, SigTraitParam, SigTraitParamKind, SigTraitParamList, SigTyKind,
            SigTyOrRe, SigTyOrReList, TraitItem, TyCtxt, TyOrReKind, TypeGeneric,
        },
    },
    symbol,
    utils::{
        hash::FxHashMap,
        lang::{SimpleListFormatGlue, format_list},
    },
};
use hashbrown::hash_map;
use std::iter;

// === Generic definition lowering === //

fn lower_generic_defs<'ast>(
    binder: &mut GenericBinder,
    ast: &'ast AstGenericParamList,
    generic_clause_lists: &mut Vec<Option<&'ast AstTraitClauseList>>,
    s: &Session,
) {
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
                        clauses: LateInit::uninit(),
                    },
                    s,
                )));

                generic_clause_lists.push(clauses);
            }
        }
    }
}

fn check_generic_defs_for_duplicates(defs: impl IntoIterator<Item = AnyGenericIdent>) {
    let mut bound_re_names = FxHashMap::default();
    let mut bound_ty_names = FxHashMap::default();

    for def in defs {
        match def {
            AnyGenericIdent::Re(def) => {
                if let Some(replaced) = bound_re_names.insert(def.name, def) {
                    Diag::span_err(def.span, "generic name used more than once")
                        .child(LeafDiag::span_note(
                            replaced.span,
                            "name previously used here",
                        ))
                        .emit();
                }
            }
            AnyGenericIdent::Ty(def) => {
                if let Some(replaced) = bound_ty_names.insert(def.text, def) {
                    Diag::span_err(def.span, "generic name used more than once")
                        .child(LeafDiag::span_note(
                            replaced.span,
                            "name previously used here",
                        ))
                        .emit();
                }
            }
        }
    }
}

impl<'ast> InterItemLowerCtxt<'_, 'ast> {
    pub fn lower_generic_defs(
        &mut self,
        binder: &mut GenericBinder,
        ast: &'ast AstGenericParamList,
        generic_clause_lists: &mut Vec<Option<&'ast AstTraitClauseList>>,
    ) {
        lower_generic_defs(binder, ast, generic_clause_lists, &self.tcx.session);
    }

    pub fn seal_generic_binder_with_checks(&mut self, binder: GenericBinder) -> Obj<GenericBinder> {
        let s = &self.tcx.session;

        check_generic_defs_for_duplicates(binder.defs.iter().map(|def| def.ident(s)));

        binder.seal(s)
    }
}

impl IntraItemLowerCtxt<'_> {
    pub fn lower_simple_generic_defs(
        &mut self,
        ast: Option<&AstGenericParamList>,
    ) -> Obj<GenericBinder> {
        let s = &self.tcx.session;
        let mut binder = GenericBinder::default();
        let mut generic_clause_lists = Vec::new();

        if let Some(ast) = ast {
            lower_generic_defs(
                &mut binder,
                ast,
                &mut generic_clause_lists,
                &self.tcx.session,
            );
        }

        check_generic_defs_for_duplicates(binder.defs.iter().map(|def| def.ident(s)));

        let binder = binder.seal(s);

        self.scoped(|this| {
            this.define_generics_in_binder(binder);
            this.lower_generic_def_clauses(binder, &generic_clause_lists);
        });

        binder
    }

    pub fn define_generics_in_binder(&mut self, binder: Obj<GenericBinder>) {
        let s = &self.tcx.session;

        for generic in &binder.r(s).defs {
            match generic {
                AnyGeneric::Re(generic) => {
                    self.generic_re_names
                        .define(generic.r(s).lifetime.name, DefinedGenericRe::Sig(*generic));
                }
                AnyGeneric::Ty(generic) => {
                    self.generic_ty_names
                        .define(generic.r(s).ident.text, DefinedGenericTy::Sig(*generic));
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
                    LateInit::init(&generic.r(s).clauses, self.lower_clauses(clause_list));
                }
            }
        }
    }

    pub fn define_hrtb_defs_for_ast(&mut self, ast: Option<&AstGenericParamList>) {
        let Some(ast) = ast else {
            return;
        };

        let range = self.generic_debruijn.move_inwards_by(ast.list.len());

        for (idx, def) in ast.list.iter().enumerate() {
            let Some(def_kind) = def.kind.as_generic_def() else {
                Diag::span_err(def.span, "expected generic parameter definition").emit();
                continue;
            };

            match def_kind {
                AstGenericDef::Re(lifetime, _clauses) => {
                    self.generic_re_names.define(
                        lifetime.name,
                        DefinedGenericRe::Hrtb(lifetime.span, range.at(idx)),
                    );
                }
                AstGenericDef::Ty(ident, _clauses) => {
                    self.generic_ty_names.define(
                        ident.text,
                        DefinedGenericTy::Hrtb(ident.span, range.at(idx)),
                    );
                }
            }
        }
    }

    pub fn check_hrtb_def_ast_for_duplicates(&mut self, ast: Option<&AstGenericParamList>) {
        let Some(ast) = ast else {
            return;
        };

        check_generic_defs_for_duplicates(ast.list.iter().filter_map(|ast| {
            Some(match ast.kind.as_generic_def()? {
                AstGenericDef::Re(lifetime, _clauses) => AnyGenericIdent::Re(lifetime),
                AstGenericDef::Ty(ident, _clauses) => AnyGenericIdent::Ty(ident),
            })
        }));
    }

    pub fn lower_hrtb_def_clauses(
        &mut self,
        ast: Option<&AstGenericParamList>,
    ) -> SigHrtbDebruijnDefList {
        let s = &self.tcx.session;

        let Some(ast) = ast else {
            return SigHrtbDebruijnDefList::new_slice(&[], s);
        };

        let defs = ast
            .list
            .iter()
            .map(|ast| match ast.kind.as_generic_def() {
                Some(AstGenericDef::Re(lifetime, clauses)) => SigHrtbDebruijnDef {
                    span: lifetime.span,
                    name: lifetime.name,
                    kind: TyOrReKind::Re,
                    clauses: self.lower_clauses(clauses),
                },
                Some(AstGenericDef::Ty(ident, clauses)) => SigHrtbDebruijnDef {
                    span: ident.span,
                    name: ident.text,
                    kind: TyOrReKind::Ty,
                    clauses: self.lower_clauses(clauses),
                },
                None => SigHrtbDebruijnDef {
                    span: Span::DUMMY,
                    name: symbol!("error"),
                    kind: TyOrReKind::Ty,
                    clauses: SigTraitClauseList {
                        span: Span::DUMMY,
                        elems: Obj::new_slice(&[], s),
                    },
                },
            })
            .collect::<Vec<_>>();

        SigHrtbDebruijnDefList::new_slice(&defs, s)
    }
}

// === Complete generic lowering routines === //

impl IntraItemLowerCtxt<'_> {
    pub fn lower_type_relative_generics(
        &mut self,
        args: Option<&AstGenericParamList>,
    ) -> Option<SigGenericList> {
        let s = &self.tcx.session;

        args.as_ref().map(|args| {
            let (positional, associated) = self.lower_generic_params_syntactic(&args.list);

            if let Some(associated) = associated.first() {
                Diag::span_err(
                    associated.span,
                    "method or enum variant does not have associated type constraints",
                )
                .emit();
            }

            SigGenericList {
                segment_span: args.span,
                elems: SigTyOrReList::new_slice(&positional, s),
            }
        })
    }

    pub fn lower_generics_of_entirely_positional(
        &mut self,
        owner: Obj<Item>,
        binder: Obj<GenericBinder>,
        segment_span: Span,
        generics: &[AstGenericParam],
    ) -> SigGenericList {
        let s = &self.tcx.session;

        let (positional, associated) = self.lower_generic_params_syntactic(generics);

        let params =
            self.normalize_positional_generic_arity(binder, None, segment_span, &positional);

        if let Some(associated) = associated.first() {
            Diag::span_err(
                associated.span,
                format_args!(
                    "{} does not have any associated type constraints",
                    owner.r(s).bare_category_path(s),
                ),
            )
            .emit();
        }

        params
    }

    pub fn lower_generics_of_trait_instance_in_fn(
        &mut self,
        def: Obj<TraitItem>,
        segment_span: Span,
        generics: Option<&AstGenericParamList>,
    ) -> SigGenericList {
        let s = &self.tcx.session;

        let Some(generics) = generics else {
            return self.construct_trait_instance_from_positionals(
                def,
                self.synthesize_inferred_generics_for_elision(
                    *def.r(s).generics,
                    Some(*def.r(s).regular_generic_count),
                    segment_span,
                ),
            );
        };

        let (positional, associated) = self.lower_generic_params_syntactic(&generics.list);

        let params = self.normalize_positional_generic_arity(
            *def.r(s).generics,
            None,
            segment_span,
            &positional,
        );

        if let Some(associated) = associated.first() {
            Diag::span_err(associated.span, "associated types cannot be specified here").emit();
        }

        self.construct_trait_instance_from_positionals(def, params)
    }

    pub fn lower_generics_of_trait_spec_in_fn(
        &mut self,
        def: Obj<TraitItem>,
        segment_span: Span,
        generics: Option<&AstGenericParamList>,
    ) -> SigTraitParamList {
        let s = &self.tcx.session;

        let Some(generics) = generics else {
            return SigTraitParamList::new_slice(
                &self.construct_trait_spec_from_positionals(
                    def,
                    self.synthesize_inferred_generics_for_elision(
                        *def.r(s).generics,
                        Some(*def.r(s).regular_generic_count),
                        segment_span,
                    ),
                ),
                s,
            );
        };

        // Lower generic parameters.
        let (positional, associated) = self.lower_generic_params_syntactic(&generics.list);

        let params = self.normalize_positional_generic_arity(
            *def.r(s).generics,
            Some(*def.r(s).regular_generic_count),
            segment_span,
            &positional,
        );
        let mut params = self.construct_trait_spec_from_positionals(def, params);

        self.lower_associated_type_generic_params(def, &mut params, &associated);

        SigTraitParamList::new_slice(&params, s)
    }

    pub fn lower_trait_instance_of_impl_block(
        &mut self,
        for_trait: &AstTy,
        body: &AstImplLikeBody,
    ) -> Result<SigTraitInstance, ErrorGuaranteed> {
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
            *def.r(s).generics,
            Some(*def.r(s).regular_generic_count),
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
            .elems
            .r(s)
            .iter()
            .copied()
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

                    let param = &mut params[generic.r(s).binder.idx as usize];

                    if let Some(old_param) = param {
                        Diag::span_err(name.span, "associated type specified more than once")
                            .child(LeafDiag::span_note(
                                old_param.span(s),
                                "type first specified here",
                            ))
                            .emit();
                    } else {
                        *param = Some(SigTyOrRe::Ty(exact_ty));
                    }
                }
                AstImplLikeMemberKind::TypeInherits(..)
                | AstImplLikeMemberKind::Fn(..)
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
                    "missing associated type{} {}",
                    if missing_mentions.len() == 1 { "" } else { "s" },
                    format_list(
                        missing_mentions.iter().map(|v| format!("`{v}`")),
                        SimpleListFormatGlue::AND_LIST,
                    )
                ),
            )
            .emit()
        });

        let params = params.iter().map(|param| {
            param.unwrap_or_else(|| {
                SigTyOrRe::Ty(SigTyKind::Error(missing_mentions.unwrap()).wrap(for_trait.span, s))
            })
        });

        let params = SigTyOrReList::new_iter(params, s);

        Ok(SigTraitInstance {
            span: for_trait.span,
            def,
            params: SigGenericList {
                segment_span: for_trait.span,
                elems: params,
            },
        })
    }
}

// === Generic parameter lowering helpers === //

#[derive(Debug, Copy, Clone)]
pub struct LoweredAssocConstraint {
    pub span: Span,
    pub name: Ident,
    pub param: SigTraitParam,
}

impl IntraItemLowerCtxt<'_> {
    pub fn lower_generic_params_syntactic(
        &mut self,
        params: &[AstGenericParam],
    ) -> (Vec<SigTyOrRe>, Vec<LoweredAssocConstraint>) {
        let mut positional = Vec::<SigTyOrRe>::new();
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

                    positional.push(SigTyOrRe::Ty(self.lower_ty(ty)));
                }
                AstGenericParamKind::PositionalRe(re) => {
                    check_ordering(re.span, &associated);

                    positional.push(SigTyOrRe::Re(self.lower_re(re)));
                }
                AstGenericParamKind::InheritTy(name, clauses) => {
                    let param = SigTraitParamKind::Unspecified(self.lower_clauses(Some(clauses)))
                        .wrap(clauses.span);

                    if check_mention(*name) {
                        associated.push(LoweredAssocConstraint {
                            span: ast_param.span,
                            name: *name,
                            param,
                        });
                    }
                }
                AstGenericParamKind::TyEquals(name, equals) => {
                    let param = SigTraitParamKind::Equals(SigTyOrRe::Ty(self.lower_ty(equals)))
                        .wrap(equals.span);

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
        orig_params: &[SigTyOrRe],
    ) -> SigGenericList {
        normalize_positional_generic_arity(
            self.tcx,
            binder,
            binder_len_override,
            segment_span,
            orig_params,
        )
    }

    pub fn synthesize_inferred_generics_for_elision(
        &self,
        binder: Obj<GenericBinder>,
        binder_len_override: Option<u32>,
        segment_span: Span,
    ) -> SigGenericList {
        let s = &self.tcx.session;

        let binder_len = binder_len_override.map_or(binder.r(s).defs.len(), |v| v as usize);

        let params = binder.r(s).defs[..binder_len]
            .iter()
            .map(|expected| match expected {
                AnyGeneric::Re(_) => SigTyOrRe::Re(SigReKind::Infer.wrap(segment_span)),
                AnyGeneric::Ty(_) => SigTyOrRe::Ty(SigTyKind::Infer.wrap(segment_span, s)),
            });

        SigGenericList {
            segment_span,
            elems: SigTyOrReList::new_iter(params, s),
        }
    }

    pub fn construct_trait_spec_from_positionals(
        &mut self,
        def: Obj<TraitItem>,
        params: SigGenericList,
    ) -> Vec<SigTraitParam> {
        let s = &self.tcx.session;

        debug_assert_eq!(
            *def.r(s).regular_generic_count as usize,
            params.elems.r(s).len()
        );

        params
            .elems
            .r(s)
            .iter()
            .map(|&ty_or_re| SigTraitParamKind::Equals(ty_or_re).wrap(ty_or_re.span(s)))
            .chain(iter::repeat(
                SigTraitParamKind::Unspecified(SigTraitClauseList {
                    span: Span::DUMMY,
                    elems: Obj::new_slice(&[], s),
                })
                .wrap(params.segment_span),
            ))
            .take(def.r(s).generics.r(s).defs.len())
            .collect::<Vec<_>>()
    }

    pub fn construct_trait_instance_from_positionals(
        &mut self,
        def: Obj<TraitItem>,
        params: SigGenericList,
    ) -> SigGenericList {
        let s = &self.tcx.session;

        debug_assert_eq!(
            *def.r(s).regular_generic_count as usize,
            params.elems.r(s).len()
        );

        let elaborated_params = params
            .elems
            .r(s)
            .iter()
            .copied()
            .chain(iter::repeat(SigTyOrRe::Ty(
                SigTyKind::Infer.wrap(params.segment_span, s),
            )))
            .take(def.r(s).generics.r(s).defs.len())
            .collect::<Vec<_>>();

        SigGenericList {
            segment_span: params.segment_span,
            elems: SigTyOrReList::new_slice(&elaborated_params, s),
        }
    }

    pub fn lower_associated_type_generic_params(
        &mut self,
        def: Obj<TraitItem>,
        params: &mut [SigTraitParam],
        associated: &[LoweredAssocConstraint],
    ) {
        let s = &self.tcx.session;

        for associated in associated {
            let Some(generic) = def.r(s).associated_types.get(&associated.name.text) else {
                Diag::span_err(
                    associated.name.span,
                    format_args!(
                        "{} does not have associated type `{}`",
                        def.r(s).item.r(s).bare_category_path(s),
                        associated.name.text,
                    ),
                )
                .emit();

                continue;
            };

            let idx = generic.r(s).binder.idx as usize;

            params[idx] = associated.param;
        }
    }
}

// === Cross-phase === //

pub fn normalize_positional_generic_arity(
    tcx: &TyCtxt,
    binder: Obj<GenericBinder>,
    binder_len_override: Option<u32>,
    segment_span: Span,
    orig_params: &[SigTyOrRe],
) -> SigGenericList {
    let s = &tcx.session;

    let binder_len = binder_len_override.map_or(binder.r(s).defs.len(), |v| v as usize);

    let mut errored_out_missing = None;

    let resolved_params = binder.r(s).defs[..binder_len]
        .iter()
        .zip(orig_params.iter().map(Some).chain(iter::repeat(None)))
        .map(|(expected, actual)| {
            let actual_span = actual.map_or(segment_span, |v| {
                v.span(s).not_dummy().unwrap_or(segment_span)
            });

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
                                    orig_params.len(),
                                ),
                            ))
                            .emit()
                    }));
                };

                match (actual, expected) {
                    (SigTyOrRe::Ty(_), AnyGeneric::Ty(_)) => Ok(actual),
                    (SigTyOrRe::Re(_), AnyGeneric::Re(_)) => Ok(actual),
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
                AnyGeneric::Re(_) => SigTyOrRe::Re(SigReKind::Error(err).wrap(actual_span)),
                AnyGeneric::Ty(_) => SigTyOrRe::Ty(SigTyKind::Error(err).wrap(actual_span, s)),
            })
        })
        .collect::<Vec<_>>();

    if orig_params.len() > binder_len {
        Diag::span_err(
            orig_params[binder_len].span(s),
            "too many generic parameters",
        )
        .child(LeafDiag::new(
            Level::Note,
            format_args!(
                "expected {} generic parameter{} but got {}",
                binder_len,
                if binder_len == 1 { "" } else { "s" },
                orig_params.len(),
            ),
        ))
        .emit();
    }

    SigGenericList {
        segment_span,
        elems: SigTyOrReList::new_slice(&resolved_params, s),
    }
}
