use crate::{
    base::Session,
    semantic::{
        analysis::{ClauseCx, TyCtxt},
        syntax::{
            AdtInstance, AnyGeneric, FloatKind, HrtbBinderKind, IntKind, Re, SimpleTyKind,
            TraitClause, TraitClauseList, TraitParam, TraitSpec, Ty, TyKind, TyOrRe,
            UniversalTyVar, UniversalTyVarSourceInfo,
        },
    },
};
use std::{fmt::Write as _, mem};

pub struct ClauseCxPrinter<'a, 'tcx> {
    ccx: &'a ClauseCx<'tcx>,
    out: String,
}

impl<'a, 'tcx> ClauseCxPrinter<'a, 'tcx> {
    pub fn new(ccx: &'a ClauseCx<'tcx>) -> Self {
        Self {
            ccx,
            out: String::new(),
        }
    }

    pub fn ccx(&self) -> &'a ClauseCx<'tcx> {
        self.ccx
    }

    pub fn session(&self) -> &'tcx Session {
        self.ccx.session()
    }

    pub fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    pub fn push_ty_or_re(&mut self, val: TyOrRe) {
        match val {
            TyOrRe::Re(re) => self.push_re(re),
            TyOrRe::Ty(ty) => self.push_ty(ty),
        }
    }

    pub fn push_re(&mut self, _re: Re) {
        // TODO
        self.out.push_str("'_");
    }

    pub fn push_ty(&mut self, ty: Ty) {
        let s = self.session();

        match *self.ccx.peel_ty_infer_var_without_poll(ty).r(s) {
            TyKind::SigThis
            | TyKind::SigInfer
            | TyKind::SigGeneric(_)
            | TyKind::SigProject(_)
            | TyKind::SigAlias(_, _) => unreachable!(),

            TyKind::Simple(kind) => self.out.push_str(match kind {
                SimpleTyKind::Never => "Never",
                SimpleTyKind::Bool => "bool",
                SimpleTyKind::Char => "char",
                SimpleTyKind::Int(IntKind::S8) => "i8",
                SimpleTyKind::Int(IntKind::S16) => "i16",
                SimpleTyKind::Int(IntKind::S32) => "i32",
                SimpleTyKind::Int(IntKind::S64) => "i64",
                SimpleTyKind::Uint(IntKind::S8) => "u8",
                SimpleTyKind::Uint(IntKind::S16) => "u16",
                SimpleTyKind::Uint(IntKind::S32) => "u32",
                SimpleTyKind::Uint(IntKind::S64) => "u64",
                SimpleTyKind::Float(FloatKind::S32) => "f32",
                SimpleTyKind::Float(FloatKind::S64) => "f64",
                SimpleTyKind::Str => "str",
            }),
            TyKind::Reference(re, muta, ty) => {
                self.out.push('&');
                self.push_re(re);
                self.out.push_str(muta.opt_space_qual().as_str(s));
                self.push_ty(ty);
            }
            TyKind::Adt(AdtInstance { def, params }) => {
                write!(&mut self.out, "{}", def.r(s).item.r(s).display_path(s)).unwrap();

                if !params.r(s).is_empty() {
                    self.out.push('<');
                    for (idx, &param) in params.r(s).iter().enumerate() {
                        if idx > 0 {
                            self.out.push_str(", ");
                        }

                        self.push_ty_or_re(param);
                    }
                    self.out.push('>');
                }
            }
            TyKind::Trait(re, muta, clauses) => {
                self.out.push('&');
                self.push_re(re);
                self.out.push_str(muta.opt_space_qual().as_str(s));
                self.push_trait_clauses(clauses);
            }
            TyKind::Tuple(types) => {
                if let [ty] = *types.r(s) {
                    self.out.push('(');
                    self.push_ty(ty);
                    self.out.push_str(",)");
                } else {
                    self.out.push('(');

                    for (idx, &ty) in types.r(s).iter().enumerate() {
                        if idx > 0 {
                            self.out.push_str(", ");
                        }
                        self.push_ty(ty);
                    }

                    self.out.push(')');
                }
            }
            TyKind::FnDef(_def) => todo!(),
            TyKind::HrtbVar(_debruijn) => todo!(),
            TyKind::InferVar(var) => {
                write!(
                    &mut self.out,
                    "?{} {{{:?}}}",
                    var.index(),
                    self.ccx.lookup_infer_ty_src_info(var),
                )
                .unwrap();
            }
            TyKind::UniversalVar(var) => self.push_universal_ty(var),

            TyKind::Error(_) => self.out.push_str("{error}"),
        }
    }

    pub fn push_universal_ty(&mut self, var: UniversalTyVar) {
        let s = self.session();

        match self.ccx.lookup_universal_ty_src_info(var) {
            UniversalTyVarSourceInfo::TraitSelf => self.out.push_str("Self"),
            UniversalTyVarSourceInfo::HrtbVar => self.out.push_str("{HRTB universal}"),
            UniversalTyVarSourceInfo::Root(generic) => {
                self.out.push_str(generic.r(s).ident.text.as_str(s))
            }
            UniversalTyVarSourceInfo::Projection(root, spec, idx) => {
                self.out.push('<');
                self.push_universal_ty(root);
                self.out.push_str(" as ");
                self.push_trait_spec(spec);
                self.out.push_str(">::");
                self.out.push_str(
                    spec.def.r(s).generics.r(s).defs[idx as usize]
                        .as_ty()
                        .unwrap()
                        .r(s)
                        .ident
                        .text
                        .as_str(s),
                );
            }
        }
    }

    pub fn push_trait_clauses(&mut self, clauses: TraitClauseList) {
        let s = self.session();

        for (idx, &clause) in clauses.r(s).iter().enumerate() {
            if idx > 0 {
                self.out.push_str(" + ");
            }

            self.push_trait_clause(clause);
        }
    }

    pub fn push_trait_clause(&mut self, clause: TraitClause) {
        let s = self.session();

        match clause {
            TraitClause::Outlives(direction, other) => {
                self.out.push_str(direction.kw().as_str(s));
                self.out.push(' ');
                self.push_ty_or_re(other);
            }
            TraitClause::Trait(binder) => {
                let HrtbBinderKind::Imported(defs) = binder.kind else {
                    unreachable!()
                };

                if !defs.r(s).is_empty() {
                    self.out.push_str("for<");

                    for (idx, def) in defs.r(s).iter().enumerate() {
                        if idx > 0 {
                            self.out.push_str(", ");
                        }

                        match def.spawned_from {
                            AnyGeneric::Re(re) => {
                                self.out.push('\'');
                                self.out.push_str(re.r(s).lifetime.name.as_str(s));
                            }
                            AnyGeneric::Ty(ty) => {
                                self.out.push_str(ty.r(s).ident.text.as_str(s));
                            }
                        }
                    }

                    self.out.push('>');
                }

                self.push_trait_spec(binder.inner);
            }
        }
    }

    pub fn push_trait_spec(&mut self, spec: TraitSpec) {
        let s = self.session();

        let TraitSpec { def, params } = spec;

        write!(&mut self.out, "{}", def.r(s).item.r(s).display_path(s)).unwrap();

        if !params.r(s).is_empty() {
            self.out.push('<');

            let regular_generic_count = *def.r(s).regular_generic_count;

            for (idx, (&actual, definition)) in params
                .r(s)
                .iter()
                .zip(&def.r(s).generics.r(s).defs)
                .enumerate()
            {
                if idx > 0 {
                    self.out.push_str(", ");
                }

                match actual {
                    TraitParam::Equals(actual) => match (actual, definition) {
                        (TyOrRe::Re(actual), AnyGeneric::Re(_definition)) => {
                            self.push_re(actual);
                        }
                        (TyOrRe::Ty(actual), AnyGeneric::Ty(definition)) => {
                            if idx >= regular_generic_count as usize {
                                self.out.push_str(definition.r(s).ident.text.as_str(s));
                                self.out.push_str(" = ");
                            }

                            self.push_ty(actual);
                        }
                        _ => unreachable!(),
                    },
                    TraitParam::Unspecified(params) => {
                        let definition = definition.as_ty().unwrap();

                        if params.r(s).is_empty() {
                            continue;
                        }

                        self.out.push_str(definition.r(s).ident.text.as_str(s));
                        self.out.push_str(": ");
                        self.push_trait_clauses(params);
                    }
                }
            }
            self.out.push('>');
        }
    }

    pub fn finish(&mut self) -> String {
        mem::take(&mut self.out)
    }
}
