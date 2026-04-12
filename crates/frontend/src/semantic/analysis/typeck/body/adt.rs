use crate::{
    base::{
        Diag, ErrorGuaranteed, LeafDiag, Level,
        arena::{HasInterner as _, Obj},
        syntax::Span,
    },
    parse::token::Ident,
    semantic::{
        analysis::BodyCtxt,
        syntax::{
            AdtCtor, AdtCtorFieldIdx, AdtCtorInstance, AdtCtorSyntax, AdtCtorUnresolved,
            HirStructExpr, Ty, TyKind,
        },
    },
    utils::{
        hash::FxHashMap,
        lang::{AND_LIST_GLUE, format_list},
    },
};
use hashbrown::hash_map;

impl BodyCtxt<'_, '_> {
    pub fn check_adt_ctor_expr(&mut self, span: Span, ctor: AdtCtorInstance) -> Ty {
        let tcx = self.tcx();
        let s = self.session();

        match ctor.def.r(s).syntax {
            AdtCtorSyntax::Unit => {
                todo!()
            }
            AdtCtorSyntax::Tuple => {
                let offending_fields = ctor
                    .def
                    .r(s)
                    .fields
                    .iter()
                    .filter(|field| !field.vis.is_visible_to(self.item(), s))
                    .collect::<Vec<_>>();

                if !offending_fields.is_empty() {
                    Diag::span_err(
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
                                AND_LIST_GLUE,
                            ),
                            if offending_fields.len() == 1 {
                                "is"
                            } else {
                                "are"
                            },
                        ),
                    )
                    .emit();
                }

                todo!()
            }
            AdtCtorSyntax::Named(_) => tcx.intern(TyKind::Error(
                Diag::span_err(
                    span,
                    format_args!(
                        "expected value, got {}",
                        ctor.def.r(s).owner.bare_identified_what(s),
                    ),
                )
                .child(LeafDiag::new(
                    Level::Note,
                    format_args!(
                        "only unit and tuple {} can be turned into functions",
                        ctor.def.r(s).owner.bare_whats()
                    ),
                ))
                .emit(),
            )),
        }
    }

    pub fn check_struct_expr(&mut self, expr: HirStructExpr) -> Ty {
        let tcx = self.tcx();
        let s = self.session();

        let ctor = match self.resolve_adt_ctor(expr.ctor) {
            Ok(v) => v,
            Err(_) => todo!(),
        };

        if !ctor.def.r(s).syntax.is_named() {
            return tcx.intern(TyKind::Error(
                Diag::span_err(
                    expr.ctor_span,
                    format_args!(
                        "expected named struct or enum variant, got {}",
                        ctor.def.r(s).owner.bare_identified_what(s),
                    ),
                )
                .emit(),
            ));
        }

        let fields = self.match_up_ctor_members(
            ctor.def,
            expr.fields.r(s).iter().map(|v| (v.name, v.init)).collect(),
            expr.rest.is_none().then_some(expr.ctor_span),
        );

        todo!()
    }

    pub fn resolve_adt_ctor(
        &mut self,
        ctor: AdtCtorUnresolved,
    ) -> Result<AdtCtorInstance, ErrorGuaranteed> {
        todo!()
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
                    format_list(missing_field_list, AND_LIST_GLUE),
                ),
            )
            .emit();
        }

        accum
    }
}
