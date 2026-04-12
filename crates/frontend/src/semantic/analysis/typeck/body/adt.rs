use crate::{
    base::{Diag, ErrorGuaranteed, arena::Obj, syntax::Span},
    parse::token::Ident,
    semantic::{
        analysis::BodyCtxt,
        syntax::{
            AdtCtor, AdtCtorFieldIdx, AdtCtorInstance, AdtCtorUnresolved, HirPatListFrontAndTail,
            HirPatListFrontAndTailLen,
        },
    },
    utils::{
        hash::FxHashMap,
        lang::{AND_LIST_GLUE, format_list},
    },
};
use hashbrown::hash_map;

impl BodyCtxt<'_, '_> {
    pub fn resolve_adt_ctor(
        &mut self,
        ctor: AdtCtorUnresolved,
    ) -> Result<AdtCtorInstance, ErrorGuaranteed> {
        todo!()
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
                        AND_LIST_GLUE,
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
                    format_list(missing_field_list, AND_LIST_GLUE),
                ),
            )
            .emit();
        }

        accum
    }
}
