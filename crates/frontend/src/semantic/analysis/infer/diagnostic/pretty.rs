use crate::{
    base::Session,
    semantic::{
        analysis::ClauseCx,
        syntax::{
            AdtInstance, AnyGeneric, FloatKind, FnInstanceInner, FnOwner, HrtbBinderKind,
            InferTyVarSourceInfo, IntKind, Re, SimpleTyKind, SimpleTySet, TraitClause,
            TraitClauseList, TraitParam, TraitSpec, Ty, TyCtxt, TyKind, TyOrRe, UniversalTyVar,
            UniversalTyVarSourceInfo,
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
                self.out.push(' ');
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
                self.out.push(' ');
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
            TyKind::FnDef(def) => {
                let FnInstanceInner { owner, early_args } = *def.r(s);

                self.out.push_str("fn @ ");

                match owner {
                    FnOwner::Item(def) => {
                        write!(&mut self.out, "{}", def.r(s).item.r(s).display_path(s)).unwrap();
                    }
                    FnOwner::Trait {
                        instance,
                        self_ty,
                        method_idx,
                    } => {
                        self.out.push_str("<");
                        self.push_ty(self_ty);
                        self.out.push_str(" as ");
                        self.push_trait_spec(instance);
                        self.out.push_str(">::");
                        self.out.push_str(
                            instance.def.r(s).methods[method_idx as usize]
                                .r(s)
                                .name
                                .text
                                .as_str(s),
                        );
                    }
                    FnOwner::Inherent {
                        self_ty,
                        block,
                        method_idx,
                    } => {
                        self.push_ty(self_ty);
                        self.out.push_str("::");
                        self.out.push_str(
                            block.r(s).methods[method_idx as usize]
                                .unwrap()
                                .r(s)
                                .name
                                .text
                                .as_str(s),
                        );
                    }
                }

                if let Some(early_args) = early_args {
                    self.out.push('<');

                    for (idx, &ty_or_re) in early_args.r(s).iter().enumerate() {
                        if idx > 0 {
                            self.out.push_str(", ");
                        }
                        self.push_ty_or_re(ty_or_re);
                    }

                    self.out.push('>');
                }
            }
            TyKind::HrtbVar(debruijn) => {
                // TODO
                write!(&mut self.out, "HrtbVar({:?})", debruijn.0).unwrap();
            }
            TyKind::InferVar(var) => {
                let set = self
                    .ccx()
                    .lookup_ty_infer_var_without_poll(var)
                    .unwrap_err()
                    .perm_set;

                if !set.intersects(SimpleTySet::OTHER) {
                    write!(
                        &mut self.out,
                        "?{} {{{}}}",
                        var.index(),
                        set.names()
                            .into_iter()
                            .map(|v| v.as_str(s))
                            .collect::<Vec<_>>()
                            .join(" | ")
                    )
                    .unwrap();
                } else {
                    match self.ccx.lookup_infer_ty_src_info(var) {
                        InferTyVarSourceInfo::HrtbLhsInstantiation { span: _, clauses } => {
                            write!(
                                &mut self.out,
                                "{{HRTB existential capture #{}: ",
                                var.index()
                            )
                            .unwrap();
                            self.push_trait_clauses(**clauses);
                            self.out.push_str("}");
                        }

                        src_info @ (InferTyVarSourceInfo::UniversalElabHelper
                        | InferTyVarSourceInfo::TraitAssocPlaceholderHelper
                        | InferTyVarSourceInfo::ProjectionResult { .. }
                        | InferTyVarSourceInfo::Imported { .. }
                        | InferTyVarSourceInfo::Local { .. }
                        | InferTyVarSourceInfo::FunctionArgs { .. }
                        | InferTyVarSourceInfo::FunctionRetVal { .. }
                        | InferTyVarSourceInfo::MethodReceiver { .. }
                        | InferTyVarSourceInfo::OverloadedResult { .. }
                        | InferTyVarSourceInfo::Literal { .. }
                        | InferTyVarSourceInfo::ForLoopElem { .. }
                        | InferTyVarSourceInfo::IndexInput { .. }
                        | InferTyVarSourceInfo::IndexOutput { .. }
                        | InferTyVarSourceInfo::LoopDemand { .. }
                        | InferTyVarSourceInfo::HoleInfer { .. }
                        | InferTyVarSourceInfo::PatType { .. }
                        | InferTyVarSourceInfo::EmptyArrayElem { .. }
                        | InferTyVarSourceInfo::UnifyHelper
                        | InferTyVarSourceInfo::DerefHelper
                        | InferTyVarSourceInfo::MethodLookupHelper) => {
                            write!(&mut self.out, "?{} {{{:?}}}", var.index(), src_info).unwrap();
                        }
                    }
                }
            }
            TyKind::UniversalVar(var) => self.push_universal_ty(var),

            TyKind::Error(_) => self.out.push_str("{error}"),
        }
    }

    pub fn push_universal_ty(&mut self, var: UniversalTyVar) {
        let s = self.session();

        match self.ccx.lookup_universal_ty_src_info(var) {
            UniversalTyVarSourceInfo::TraitSelf => self.out.push_str("Self"),
            UniversalTyVarSourceInfo::HrtbVar => {
                write!(&mut self.out, "{{HRTB universal capture #{}: ", var.index()).unwrap();
                self.push_trait_clauses(
                    self.ccx.direct_ty_universal_clauses_possibly_floating(var),
                );
                self.out.push_str("}");
            }
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

                    self.out.push_str("> ");
                }

                self.push_trait_spec(binder.inner);
            }
        }
    }

    pub fn push_trait_spec(&mut self, spec: TraitSpec) {
        let s = self.session();

        let TraitSpec { def, params } = spec;

        write!(&mut self.out, "{}", def.r(s).item.r(s).display_path(s)).unwrap();

        let regular_generic_count = *def.r(s).regular_generic_count;
        let mut idx = 0;

        fn fmt_arg<'a, 'tcx>(
            me: &mut ClauseCxPrinter<'a, 'tcx>,
            idx: &mut usize,
            f: impl FnOnce(&mut ClauseCxPrinter<'a, 'tcx>),
        ) {
            if *idx == 0 {
                me.out.push('<');
            } else {
                me.out.push_str(", ");
            }

            f(me);

            *idx += 1;
        }

        for (&actual, definition) in params.r(s).iter().zip(&def.r(s).generics.r(s).defs) {
            match actual {
                TraitParam::Equals(actual) => match (actual, definition) {
                    (TyOrRe::Re(actual), AnyGeneric::Re(_definition)) => {
                        fmt_arg(self, &mut idx, |this| this.push_re(actual));
                    }
                    (TyOrRe::Ty(actual), AnyGeneric::Ty(definition)) => {
                        fmt_arg(self, &mut idx, |this| {
                            if definition.r(s).binder.idx >= regular_generic_count {
                                this.out.push_str(definition.r(s).ident.text.as_str(s));
                                this.out.push_str(" = ");
                            }

                            this.push_ty(actual);
                        });
                    }
                    _ => unreachable!(),
                },
                TraitParam::Unspecified(params) => {
                    let definition = definition.as_ty().unwrap();

                    if params.r(s).is_empty() {
                        continue;
                    }

                    fmt_arg(self, &mut idx, |this| {
                        this.out.push_str(definition.r(s).ident.text.as_str(s));
                        this.out.push_str(": ");
                        this.push_trait_clauses(params);
                    });
                }
            }
        }

        if idx > 0 {
            self.out.push('>');
        }
    }

    pub fn finish(&mut self) -> String {
        mem::take(&mut self.out)
    }
}
