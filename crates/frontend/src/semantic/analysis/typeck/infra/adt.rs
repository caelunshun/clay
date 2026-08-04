use crate::{
    base::{
        Diag, ErrorGuaranteed,
        arena::{HasInterner, Obj},
        syntax::Span,
    },
    parse::token::Ident,
    semantic::{
        analysis::typeck::BodyCtxt,
        infer::HrtbUniverse,
        syntax::{
            AdtCtor, AdtCtorFieldIdx, AdtCtorInstance, AdtCtorUnresolved, AdtInstance, AdtKind,
            HirPatListFrontAndTail, HirPatListFrontAndTailLen, Ty, TyKind,
        },
    },
    utils::{
        hash::FxHashMap,
        lang::{SimpleListFormatGlue, format_list},
    },
};
use hashbrown::hash_map;

// TODO: Can we support late-bound ctors too?

impl BodyCtxt<'_, '_> {
    pub fn resolve_adt_ctor(
        &mut self,
        span: Span,
        ctor: AdtCtorUnresolved,
    ) -> Result<AdtCtorInstance, ErrorGuaranteed> {
        let s = self.session();
        let tcx = self.tcx();

        let import_env = self.import_env;

        match ctor {
            AdtCtorUnresolved::ResolvedTy(ty) => {
                let ty = self
                    .ccx_mut()
                    .import_report_here(HrtbUniverse::ROOT_REF, import_env, ty);

                self.resolve_ty_as_adt_ctor_instance(span, ty)
            }
            AdtCtorUnresolved::ResolvedEnumVariant(def, args) => Ok(AdtCtorInstance {
                def: *def.r(s).adt_variant(s).r(s).ctor,
                params: self
                    .ccx_mut()
                    .import_report_here(
                        HrtbUniverse::ROOT_REF,
                        import_env,
                        SpannedAdtInstanceView {
                            def: def.r(s).adt(s),
                            params: args,
                        }
                        .encode(span, tcx),
                    )
                    .params,
            }),
            AdtCtorUnresolved::UnresolvedEnumVariant(enum_ty, variant_name) => {
                let enum_ty =
                    self.ccx_mut()
                        .import_report_here(HrtbUniverse::ROOT_REF, import_env, enum_ty);

                let enum_instance = self.resolve_ty_as_adt_instance(span, enum_ty)?;

                let def = match *enum_instance.def.r(s).kind {
                    AdtKind::Enum(def) => def,
                    AdtKind::Struct(_) => {
                        return Err(Diag::span_err(
                            variant_name.span,
                            "unexpected path segment after struct",
                        )
                        .emit());
                    }
                };

                let Some(&def_idx) = def.r(s).by_name.get(&variant_name.text) else {
                    return Err(Diag::span_err(variant_name.span, "unknown enum variant").emit());
                };

                let def = (*def.r(s).variants)[def_idx];

                Ok(AdtCtorInstance {
                    def: *def.r(s).ctor,
                    params: enum_instance.params,
                })
            }
        }
    }

    pub fn adt_ctor_to_instance_ty(&self, ctor: AdtCtorInstance) -> Ty {
        let s = self.session();
        let tcx = self.tcx();

        tcx.intern(TyKind::Adt(AdtInstance {
            def: ctor.def.r(s).owner.item(s),
            params: ctor.params,
        }))
    }

    pub fn resolve_ty_as_adt_ctor_instance(
        &mut self,
        span: Span,
        ty: Ty,
    ) -> Result<AdtCtorInstance, ErrorGuaranteed> {
        let s = self.session();

        let instance = self.resolve_ty_as_adt_instance(span, ty)?;
        let def = match *instance.def.r(s).kind {
            AdtKind::Struct(def) => *def.r(s).ctor,
            AdtKind::Enum(_) => {
                return Err(Diag::span_err(span, "expected enum variant, got bare enum").emit());
            }
        };

        Ok(AdtCtorInstance {
            def,
            params: instance.params,
        })
    }

    pub fn resolve_ty_as_adt_instance(
        &mut self,
        span: Span,
        ty: Ty,
    ) -> Result<AdtInstance, ErrorGuaranteed> {
        let s = self.session();

        match *self.ccx_mut().peel_ty_infer_var_after_poll(ty).r(s) {
            TyKind::Adt(instance) => Ok(instance),

            TyKind::Simple(..)
            | TyKind::Reference(..)
            | TyKind::Trait(..)
            | TyKind::Tuple(..)
            | TyKind::FnDef(..)
            | TyKind::InferVar(..)
            | TyKind::UniversalVar(..) => {
                return Err(Diag::span_err(
                    span,
                    format_args!(
                        "expected ADT constructor; got `{}`",
                        self.ccx.pretty().wrap(ty),
                    ),
                )
                .emit());
            }

            TyKind::SigThis
            | TyKind::SigInfer
            | TyKind::SigGeneric(..)
            | TyKind::SigProject(..)
            | TyKind::SigAlias(..)
            | TyKind::HrtbVar(..) => unreachable!(),

            TyKind::Error(err) => return Err(err),
        }
    }

    pub fn check_tuple_ctor_visibilities(
        &mut self,
        span: Span,
        ctor: AdtCtorInstance,
    ) -> Result<(), ErrorGuaranteed> {
        let s = self.session();

        let offending_fields = ctor
            .def
            .r(s)
            .fields
            .iter()
            .filter(|field| !field.vis.is_visible_to(self.item(), s))
            .collect::<Vec<_>>();

        if offending_fields.is_empty() {
            Ok(())
        } else {
            Err(Diag::span_err(
                span,
                format_args!(
                    "tuple constructor for {} is not visible to {} because field{} {} {} \
                             inaccessible",
                    ctor.def.r(s).owner.bare_identified_what(s),
                    self.item().r(s).bare_category_path(s),
                    if offending_fields.len() == 1 { "" } else { "s" },
                    format_list(
                        offending_fields
                            .iter()
                            .map(|v| format!("`{}`", v.idx.raw())),
                        SimpleListFormatGlue::AND_LIST,
                    ),
                    if offending_fields.len() == 1 {
                        "is"
                    } else {
                        "are"
                    },
                ),
            )
            .emit())
        }
    }

    pub fn check_pat_tuple_visibilities(
        &mut self,
        span: Span,
        ctor: AdtCtorInstance,
        children: HirPatListFrontAndTail,
    ) {
        let s = self.session();

        let expected_len = ctor.def.r(s).fields.len() as u32;

        let arity_offense = match children.len(s) {
            HirPatListFrontAndTailLen::Exactly(v) if v != expected_len => Some((v, "", "")),
            HirPatListFrontAndTailLen::AtLeast(v) if v > expected_len => {
                Some((v, " at least", "only "))
            }
            _ => None,
        };

        if let Some((child_count, at_least, only)) = arity_offense {
            Diag::span_err(
                span,
                format_args!(
                    "this pattern has{at_least} {child_count} field{}, but the \
                     corresponding tuple {} {only}has {}",
                    if child_count == 1 { "" } else { "s" },
                    ctor.def.r(s).owner.bare_identified_what(s),
                    expected_len,
                ),
            )
            .emit();
        }

        let front_fields = children.front.r(s).iter().zip(&ctor.def.r(s).fields);

        let back_fields = children
            .tail
            .iter()
            .flat_map(|v| v.r(s).iter())
            .zip(ctor.def.r(s).fields.iter().rev());

        for (pat, field) in front_fields.chain(back_fields) {
            if field.vis.is_visible_to(self.item(), s) {
                continue;
            }

            Diag::span_err(
                pat.r(s).span,
                format_args!(
                    "field `{}` of {} is not visible to {}",
                    field.idx.raw(),
                    ctor.def.r(s).owner.bare_identified_what(s),
                    self.item().r(s).bare_category_path(s),
                ),
            )
            .emit();
        }
    }

    pub fn match_up_ctor_members<T>(
        &self,
        ctor: Obj<AdtCtor>,
        fields: Vec<(Ident, T)>,
        deny_missing: Option<Span>,
    ) -> Vec<(AdtCtorFieldIdx, T)> {
        let s = self.session();
        let name_map = ctor.r(s).syntax.unwrap_names();

        let mut mentions = FxHashMap::default();
        let mut accum = Vec::new();

        for (name, value) in fields {
            let Some(&resolved_idx) = name_map.get(&name.text) else {
                Diag::span_err(
                    name.span,
                    format_args!(
                        "{} does not have field `{}`",
                        ctor.r(s).owner.bare_identified_what(s),
                        name.text
                    ),
                )
                .emit();

                continue;
            };

            if !ctor.r(s).fields[resolved_idx]
                .vis
                .is_visible_to(self.item(), s)
            {
                Diag::span_err(
                    name.span,
                    format_args!(
                        "field `{}` is not visible to {}",
                        name.text,
                        self.item().r(s).bare_category_path(s)
                    ),
                )
                .emit();
            }

            match mentions.entry(resolved_idx) {
                hash_map::Entry::Vacant(entry) => {
                    entry.insert(name.span);
                }
                hash_map::Entry::Occupied(entry) => {
                    Diag::anon_err(format_args!("field `{}` used more than once", name.text))
                        .primary(name.span, "used here again")
                        .secondary(*entry.get(), "first used here")
                        .emit();

                    continue;
                }
            }

            accum.push((resolved_idx, value));
        }

        if let Some(deny_missing) = deny_missing
            && ctor.r(s).fields.len() != accum.len()
        {
            let mut missing_field_list = Vec::new();

            for (idx, field_info) in ctor.r(s).fields.iter_enumerated() {
                if mentions.contains_key(&idx) {
                    continue;
                }

                missing_field_list.push(field_info.ident.unwrap().text);
            }

            Diag::span_err(
                deny_missing,
                format_args!(
                    "{} is missing field{}: {}",
                    ctor.r(s).owner.bare_identified_what(s),
                    if missing_field_list.len() == 1 {
                        ""
                    } else {
                        "s"
                    },
                    format_list(missing_field_list, SimpleListFormatGlue::AND_LIST,),
                ),
            )
            .emit();
        }

        accum
    }
}
