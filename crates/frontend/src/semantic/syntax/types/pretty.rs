use crate::{
    base::{Session, arena::HasInterner},
    semantic::{
        analysis::ClauseCx,
        syntax::{
            AdtInstance, AnyGeneric, FloatKind, FnInstanceInner, FnOwner, HrtbBinder,
            HrtbBinderKind, InferTyVarSourceInfo, IntKind, Re, SimpleTyKind, SimpleTySet,
            TraitClause, TraitClauseList, TraitParam, TraitSpec, Ty, TyKind, TyOrRe, TyProjection,
            UniversalTyVar, UniversalTyVarSourceInfo,
        },
    },
};
use std::{
    cell::Cell,
    fmt::{self, Write},
    ptr::NonNull,
};

// === Options === //

thread_local! {
    static OPTS: Cell<Option<NonNull<()>>> = const { Cell::new(None) };
}

pub struct PrettyPrinterOpts<'a, 'tcx> {
    pub ccx: Option<&'a ClauseCx<'tcx>>,
}

impl<'a, 'tcx> PrettyPrinterOpts<'a, 'tcx> {
    pub fn provide<R>(&self, f: impl FnOnce() -> R) -> R {
        let _guard = scopeguard::guard(
            OPTS.replace(Some(NonNull::from(self).cast::<()>())),
            |old| OPTS.set(old),
        );

        f()
    }

    pub fn fetch<R>(f: impl FnOnce(&PrettyPrinterOpts<'_, '_>) -> R) -> R {
        f(match OPTS.get() {
            Some(cx) => unsafe { cx.cast::<PrettyPrinterOpts<'_, '_>>().as_ref() },
            None => &PrettyPrinterOpts { ccx: None },
        })
    }

    pub fn fetch_ccx<R>(f: impl FnOnce(Option<&ClauseCx>) -> R) -> R {
        Self::fetch(|opts| f(opts.ccx))
    }
}

// === Printing === //

macro_rules! forward_display {
    ($($ty:ty),*$(,)?) => {$(
        impl fmt::Display for $ty {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Debug::fmt(self, f)
            }
        }
    )*};
}

forward_display! {
    TyOrRe,
    Re,
    HrtbBinder,
    Ty,
    PrettyUniversalTyVar,
    PrettyTraitClauseList,
    TraitClause,
    TraitSpec,
}

impl fmt::Debug for TyOrRe {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            TyOrRe::Re(v) => v.fmt(f),
            TyOrRe::Ty(v) => v.fmt(f),
        }
    }
}

impl fmt::Debug for Re {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO
        f.write_str("'_")
    }
}

impl fmt::Debug for HrtbBinder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = &Session::fetch();

        match self.kind {
            HrtbBinderKind::Signature(_) => {
                f.write_str("for<SIGNATURE:...>")?;
            }
            HrtbBinderKind::Imported(clauses) => {
                if !clauses.r(s).is_empty() {
                    f.write_str("for<")?;
                    for (i, clause) in clauses.r(s).iter().enumerate() {
                        if i > 0 {
                            f.write_str(", ")?;
                        }
                        match clause.spawned_from {
                            AnyGeneric::Re(generic) => {
                                write!(f, "'{}", generic.r(s).lifetime.name)?;
                            }
                            AnyGeneric::Ty(generic) => {
                                write!(f, "{}", generic.r(s).ident.text)?;
                            }
                        }

                        if !clause.clauses.r(s).is_empty() {
                            write!(f, ": {}", PrettyTraitClauseList(clause.clauses))?;
                        }
                    }
                    f.write_str("> ")?;
                }
            }
        }

        write!(f, "{}", self.inner)?;

        Ok(())
    }
}

impl fmt::Debug for TyKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = &Session::fetch();

        let ty = PrettyPrinterOpts::fetch_ccx(|ccx| {
            let Some(ccx) = ccx else {
                return *self;
            };

            *ccx.peel_ty_infer_var_without_poll(ccx.tcx().intern(*self))
                .r(s)
        });

        match ty {
            TyKind::SigThis => f.write_str("SIGNATURE:Self")?,
            TyKind::SigInfer => f.write_str("SIGNATURE:Infer")?,
            TyKind::SigGeneric(_) => f.write_str("SIGNATURE:Generic")?,

            TyKind::SigProject(TyProjection {
                target,
                spec,
                assoc,
            }) => {
                write!(
                    f,
                    "<{target} as {spec}>::{}",
                    spec.def.r(s).generics.r(s).defs[assoc as usize]
                        .as_ty()
                        .unwrap()
                        .r(s)
                        .ident
                        .text
                        .as_str(s),
                )?;
            }
            TyKind::SigAlias(def, params) => {
                write!(f, "{}", def.r(s).item.r(s).display_path(s))?;

                if !params.r(s).is_empty() {
                    f.write_char('<')?;
                    for (idx, &param) in params.r(s).iter().enumerate() {
                        if idx > 0 {
                            f.write_str(", ")?;
                        }

                        write!(f, "{param}")?;
                    }
                    f.write_char('>')?;
                }
            }

            TyKind::Simple(kind) => f.write_str(match kind {
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
            })?,
            TyKind::Reference(re, muta, ty) => {
                write!(f, "&{re} {} {ty}", muta.opt_space_qual())?;
            }
            TyKind::Adt(AdtInstance { def, params }) => {
                write!(f, "{}", def.r(s).item.r(s).display_path(s))?;

                if !params.r(s).is_empty() {
                    f.write_char('<')?;
                    for (idx, &param) in params.r(s).iter().enumerate() {
                        if idx > 0 {
                            f.write_str(", ")?;
                        }

                        write!(f, "{param}")?;
                    }
                    f.write_char('>')?;
                }
            }
            TyKind::Trait(re, muta, clauses) => {
                write!(
                    f,
                    "&{re} {} {}",
                    muta.opt_space_qual(),
                    PrettyTraitClauseList(clauses),
                )?;
            }
            TyKind::Tuple(types) => {
                if let [ty] = *types.r(s) {
                    write!(f, "({ty},)")?;
                } else {
                    f.write_char('(')?;

                    for (idx, &ty) in types.r(s).iter().enumerate() {
                        if idx > 0 {
                            f.write_str(", ")?;
                        }

                        write!(f, "{ty}")?;
                    }

                    f.write_char(')')?;
                }
            }
            TyKind::FnDef(def) => {
                let FnInstanceInner { owner, early_args } = *def.r(s);

                f.write_str("fn @ ")?;

                match owner {
                    FnOwner::Item(def) => {
                        write!(f, "{}", def.r(s).item.r(s).display_path(s))?;
                    }
                    FnOwner::Trait {
                        instance,
                        self_ty,
                        method_idx,
                    } => {
                        write!(
                            f,
                            "<{self_ty} as {instance}>::{}",
                            instance.def.r(s).methods[method_idx as usize]
                                .r(s)
                                .name
                                .text
                        )?;
                    }
                    FnOwner::Inherent {
                        self_ty,
                        block,
                        method_idx,
                    } => {
                        write!(
                            f,
                            "{self_ty}::{}",
                            block.r(s).methods[method_idx as usize]
                                .unwrap()
                                .r(s)
                                .name
                                .text
                        )?;
                    }
                }

                if let Some(early_args) = early_args {
                    f.write_char('<')?;

                    for (idx, &ty_or_re) in early_args.r(s).iter().enumerate() {
                        if idx > 0 {
                            f.write_str(", ")?;
                        }

                        write!(f, "{ty_or_re}")?;
                    }

                    f.write_char('>')?;
                }
            }
            TyKind::HrtbVar(debruijn) => {
                // TODO
                write!(f, "HrtbVar({:?})", debruijn.0)?;
            }
            TyKind::InferVar(var) => {
                PrettyPrinterOpts::fetch_ccx(|ccx| -> fmt::Result {
                    let Some(ccx) = ccx else {
                        write!(f, "?{var:?}")?;
                        return Ok(());
                    };

                    let set = ccx
                        .lookup_ty_infer_var_without_poll(var)
                        .unwrap_err()
                        .perm_set;

                    if !set.intersects(SimpleTySet::OTHER) {
                        write!(
                            f,
                            "?{} {{{}}}",
                            var.index(),
                            set.names()
                                .into_iter()
                                .map(|v| v.as_str(s))
                                .collect::<Vec<_>>()
                                .join(" | ")
                        )?;
                    } else {
                        match ccx.lookup_infer_ty_src_info(var) {
                            InferTyVarSourceInfo::HrtbLhsInstantiation { span: _, clauses } => {
                                write!(
                                    f,
                                    "{{HRTB existential capture #{}: {}}}",
                                    var.index(),
                                    PrettyTraitClauseList(**clauses),
                                )?;
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
                                write!(f, "?{} {{{:?}}}", var.index(), src_info)?;
                            }
                        }
                    }

                    Ok(())
                })?;
            }
            TyKind::UniversalVar(var) => write!(f, "{}", PrettyUniversalTyVar(var))?,

            TyKind::Error(_) => f.write_str("{error}")?,
        }

        Ok(())
    }
}

#[derive(Copy, Clone)]
pub struct PrettyUniversalTyVar(pub UniversalTyVar);

impl fmt::Debug for PrettyUniversalTyVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = &Session::fetch();

        PrettyPrinterOpts::fetch_ccx(|ccx| -> fmt::Result {
            let Some(ccx) = ccx else {
                write!(f, "u{:?}", self.0)?;
                return Ok(());
            };

            match ccx.lookup_universal_ty_src_info(self.0) {
                UniversalTyVarSourceInfo::TraitSelf => f.write_str("Self")?,
                UniversalTyVarSourceInfo::HrtbVar => {
                    write!(
                        f,
                        "{{HRTB universal capture #{}: {}}}",
                        self.0.index(),
                        PrettyTraitClauseList(
                            ccx.direct_ty_universal_clauses_possibly_floating(self.0)
                        ),
                    )?;
                }
                UniversalTyVarSourceInfo::Root(generic) => {
                    f.write_str(generic.r(s).ident.text.as_str(s))?;
                }
                UniversalTyVarSourceInfo::Projection(root, spec, idx) => {
                    write!(
                        f,
                        "<{} as {spec}>::{}",
                        PrettyUniversalTyVar(root),
                        spec.def.r(s).generics.r(s).defs[idx as usize]
                            .as_ty()
                            .unwrap()
                            .r(s)
                            .ident
                            .text
                    )?;
                }
            }

            Ok(())
        })
    }
}

#[derive(Copy, Clone)]
pub struct PrettyTraitClauseList(pub TraitClauseList);

impl fmt::Debug for PrettyTraitClauseList {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = &Session::fetch();

        for (idx, &clause) in self.0.r(s).iter().enumerate() {
            if idx > 0 {
                f.write_str(" + ")?;
            }

            write!(f, "{clause}")?;
        }

        Ok(())
    }
}

impl fmt::Debug for TraitClause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = &Session::fetch();

        match *self {
            TraitClause::Outlives(direction, other) => {
                write!(f, "{} {other}", direction.kw())?;
            }
            TraitClause::Trait(binder) => {
                match binder.kind {
                    HrtbBinderKind::Signature(_) => {
                        f.write_str("for<SIGNATURE:...>")?;
                    }
                    HrtbBinderKind::Imported(defs) => {
                        if !defs.r(s).is_empty() {
                            f.write_str("for<")?;

                            for (idx, def) in defs.r(s).iter().enumerate() {
                                if idx > 0 {
                                    f.write_str(", ")?;
                                }

                                match def.spawned_from {
                                    AnyGeneric::Re(re) => {
                                        write!(f, "'{}", re.r(s).lifetime.name)?;
                                    }
                                    AnyGeneric::Ty(ty) => {
                                        write!(f, "{}", ty.r(s).ident.text)?;
                                    }
                                }
                            }

                            f.write_str("> ")?;
                        }
                    }
                }

                write!(f, "{}", binder.inner)?;
            }
        }

        Ok(())
    }
}

impl fmt::Debug for TraitSpec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = &Session::fetch();

        let TraitSpec { def, params } = *self;

        write!(f, "{}", def.r(s).item.r(s).display_path(s))?;

        let regular_generic_count = *def.r(s).regular_generic_count;
        let mut idx = 0;

        fn fmt_arg<'a>(
            f: &mut fmt::Formatter<'a>,
            idx: &mut usize,
            op: impl FnOnce(&mut fmt::Formatter<'a>) -> fmt::Result,
        ) -> fmt::Result {
            if *idx == 0 {
                f.write_char('<')?;
            } else {
                f.write_str(", ")?;
            }

            op(f)?;

            *idx += 1;

            Ok(())
        }

        for (&actual, definition) in params.r(s).iter().zip(&def.r(s).generics.r(s).defs) {
            match actual {
                TraitParam::Equals(actual) => match (actual, definition) {
                    (TyOrRe::Re(actual), AnyGeneric::Re(_definition)) => {
                        fmt_arg(f, &mut idx, |f| write!(f, "{actual}"))?;
                    }
                    (TyOrRe::Ty(actual), AnyGeneric::Ty(definition)) => {
                        fmt_arg(f, &mut idx, |f| {
                            if definition.r(s).binder.idx >= regular_generic_count {
                                write!(f, "{} = ", definition.r(s).ident.text)?;
                            }

                            write!(f, "{actual}")?;
                            Ok(())
                        })?;
                    }
                    _ => unreachable!(),
                },
                TraitParam::Unspecified(params) => {
                    let definition = definition.as_ty().unwrap();

                    if params.r(s).is_empty() {
                        continue;
                    }

                    fmt_arg(f, &mut idx, |f| {
                        write!(
                            f,
                            "{}: {}",
                            definition.r(s).ident.text,
                            PrettyTraitClauseList(params)
                        )
                    })?;
                }
            }
        }

        if idx > 0 {
            f.write_char('>')?;
        }

        Ok(())
    }
}
