use crate::{
    base::{Session, analysis::DebruijnMap, arena::Obj, syntax::Symbol},
    semantic::{
        infer::ClauseCx,
        syntax::{
            AdtCtorOwner, AdtInstance, FloatKind, FnInstance, FnOwner, FnOwnerAdtCtor,
            FnOwnerInherent, FnOwnerTrait, HrtbBinder, HrtbDebruijn, HrtbDebruijnDef,
            HrtbProjection, InferTyVar, IntKind, Item, Re, SimpleTyKind, SimpleTySet, TraitClause,
            TraitClauseList, TraitParam, TraitSpec, Ty, TyCtxt, TyKind, TyOrRe, TyOrReList,
            UniversalReVar, UniversalReVarSourceInfo, UniversalTy, UniversalTyProj,
            UniversalTyRoot, UniversalTyVarSourceInfo,
        },
    },
    utils::lang::{SimpleListFormatGlue, format_list, format_list_into},
};
use std::{
    cell::RefCell,
    fmt::{self, Write},
};

// === PrettyFmtCx === //

impl<'tcx> ClauseCx<'tcx> {
    pub fn pretty(&self, opts: PrettyFmtOpts) -> PrettyFmtCx<'_, 'tcx> {
        PrettyFmtCx::new(self, opts)
    }
}

pub struct PrettyFmtCx<'a, 'tcx> {
    ccx: &'a ClauseCx<'tcx>,
    opts: PrettyFmtOpts,
    fmt_state: RefCell<FmtState>,
}

#[derive(Debug, Clone, Default)]
pub struct PrettyFmtOpts {
    pub verbose: bool,
}

#[derive(Default)]
struct FmtState {
    hrtb_defs: DebruijnMap<Symbol>,
}

impl<'a, 'tcx> PrettyFmtCx<'a, 'tcx> {
    pub fn new(ccx: &'a ClauseCx<'tcx>, opts: PrettyFmtOpts) -> Self {
        Self {
            ccx,
            opts,
            fmt_state: RefCell::default(),
        }
    }

    pub fn ccx(&self) -> &'a ClauseCx<'tcx> {
        self.ccx
    }

    pub fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    pub fn session(&self) -> &'tcx Session {
        self.ccx.session()
    }

    pub fn wrap<T>(&self, value: T) -> PrettyFmt<'_, 'tcx, T> {
        PrettyFmt { cx: self, value }
    }
}

// === PrettyFmt === //

pub struct PrettyFmt<'a, 'tcx, T> {
    pub cx: &'a PrettyFmtCx<'a, 'tcx>,
    pub value: T,
}

impl<'a, 'tcx, T: Copy> fmt::Display for PrettyFmt<'a, 'tcx, &'a T>
where
    PrettyFmt<'a, 'tcx, T>: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.cx.wrap(*self.value).fmt(f)
    }
}

macro_rules! impl_pretty {
    ($($ty:ty => |$cx:ident, $value:ident, $f:ident| { $($body:tt)*})*) => {$(
        impl fmt::Display for PrettyFmt<'_, '_, $ty> {
            fn fmt(&self, #[allow(unused)] $f: &mut fmt::Formatter<'_>) -> fmt::Result {
                #[allow(unused)]
                let PrettyFmt { cx: $cx, value: $value } = *self;
                $($body)*
            }
        }
    )*};
}

impl_pretty! {
    TyOrRe => |cx, value, f| {
        match value {
            TyOrRe::Re(re) => cx.wrap(re).fmt(f),
            TyOrRe::Ty(ty) => cx.wrap(ty).fmt(f),
        }
    }
    Re => |cx, value, f| {
        // TODO
        match value {
            Re::Gc => f.write_str("'gc"),
            Re::HrtbVar(debruijn) => write!(f, "'{}", cx.wrap(debruijn)),
            Re::InferVar(infer) => write!(f, "'?{}", infer.index()),
            Re::UniversalVar(re) => cx.wrap(re).fmt(f),
            Re::Erased => f.write_str("'erased"),
            Re::Error(_) => f.write_str("'error"),
        }
    }
    UniversalReVar => |cx, value, f| {
        let s = cx.session();

        match cx.ccx().lookup_universal_re_src_info(value) {
            UniversalReVarSourceInfo::Root(re) => {
                write!(f, "'{}", re.r(s).lifetime.name)
            },
            // TODO
            | UniversalReVarSourceInfo::ElaboratedLub
            | UniversalReVarSourceInfo::HrtbVar
            | UniversalReVarSourceInfo::HrtbWf { .. }
            | UniversalReVarSourceInfo::MirLocal(..) => {
                write!(f, "'u{:?}", value)
            }
        }
    }
    Ty => |cx, value, f| {
        let s = cx.session();

        match *value.r(s) {
            TyKind::Simple(kind) => cx.wrap(kind).fmt(f),
            TyKind::Reference(lt, muta, pointee) => {
                write!(f, "&{} {}{}", cx.wrap(lt), muta.opt_space_qual(), cx.wrap(pointee))
            },
            TyKind::Adt(instance) => cx.wrap(instance).fmt(f),
            TyKind::Trait(lt, muta, clauses) => {
                write!(f, "&{} {}dyn {}", cx.wrap(lt), muta.opt_space_qual(), cx.wrap(clauses))
            },
            TyKind::Tuple(types) => {
                if let [unique] = types.r(s) {
                    write!(f, "({},)", cx.wrap(unique))
                } else {
                    write!(
                        f,
                        "({})",
                        format_list(
                            types.r(s).iter().map(|value| cx.wrap(value)),
                            SimpleListFormatGlue::COMMA_LIST,
                        ),
                    )
                }
            },
            TyKind::FnDef(def) => cx.wrap(def).fmt(f),
            TyKind::HrtbVar(var) => cx.wrap(var).fmt(f),
            TyKind::HrtbProjection(HrtbProjection { target, spec, assoc_idx }) => {
                write!(
                    f,
                    "<{} as {}>::{}",
                    cx.wrap(target),
                    cx.wrap(spec),
                    spec.def
                        .r(s)
                        .generics
                        .r(s)
                        .defs[assoc_idx as usize]
                        .ident(s)
                        .text(),
                )
            },
            TyKind::InferVar(var) => cx.wrap(var).fmt(f),
            TyKind::Universal(var) => cx.wrap(var).fmt(f),
            TyKind::Error(_) => f.write_str("<error>"),
        }
    }
    SimpleTyKind => |cx, value, f| {
        f.write_str(match value {
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
        })
    }
    AdtInstance => |cx, value, f| {
        let s = cx.session();
        let AdtInstance { def, params } = value;

        f.write_str(&fmt_simple_ctor(cx, def.r(s).item, params))
    }
    TraitClauseList => |cx, value, f| {
        let s = cx.session();

        format_list_into(
            f,
            value.r(s).iter().map(|clause| cx.wrap(clause)),
            SimpleListFormatGlue::PLUS_LIST,
        )
    }
    TraitClause => |cx, value, f| {
        match value {
            TraitClause::Outlives(dir, other) => {
                write!(f, "{} {}", dir.kw(), cx.wrap(other))
            },
            TraitClause::Trait(binder) => cx.wrap(binder).fmt(f),
        }
    }
    HrtbBinder => |cx, value, f| {
        let s = cx.session();
        let HrtbBinder { defs, inner } = value;

        if !defs.r(s).is_empty() {
            f.write_str("for<")?;

            format_list_into(
                f,
                defs.r(s).iter().map(|def| cx.wrap(def)),
                SimpleListFormatGlue::COMMA_LIST,
            )?;

            f.write_str("> ")?;
        }

        let count = cx.fmt_state
            .borrow_mut()
            .hrtb_defs
            .push(defs.r(s).iter().map(|v| v.name));

        cx.wrap(inner).fmt(f)?;

        cx.fmt_state
            .borrow_mut()
            .hrtb_defs
            .pop(count);

        Ok(())
    }
    HrtbDebruijnDef => |cx, value, f| {
        let s = cx.session();
        let HrtbDebruijnDef { span: _, name, kind: _, clauses } = value;

        f.write_str(name.as_str(s))?;

        if clauses.r(s).is_empty() {
            return Ok(());
        }

        write!(f, ": {}", cx.wrap(clauses))?;

        Ok(())
    }
    HrtbDebruijn => |cx, value, f| {
        match cx.fmt_state.borrow().hrtb_defs.try_lookup(value.0) {
            Some(name) => name.fmt(f),
            None => write!(f, "debruijn({})", value.0.idx()),
        }
    }
    TraitSpec => |cx, value, f| {
        let s = cx.session();
        let TraitSpec { def, params } = value;

        cx.wrap(def.r(s).item).fmt(f)?;

        let generics = format_list(
            params.r(s)
                .iter()
                .enumerate()
                .filter_map(|(def_idx, para)| {
                    if def_idx < *def.r(s).regular_generic_count as usize {
                        let TraitParam::Equals(para) = *para else {
                            unreachable!()
                        };

                        return Some(cx.wrap(para).to_string());
                    }

                    let name = def.r(s).generics.r(s).defs[def_idx].ident(s).text();

                    match para {
                        TraitParam::Equals(para) => Some(format!("{name} = {}", cx.wrap(para))),
                        TraitParam::Unspecified(clauses) => {
                            if !clauses.r(s).is_empty() {
                                Some(format!("{name}: {}", cx.wrap(clauses)))
                            } else {
                                None
                            }
                        },
                    }
                }),
            SimpleListFormatGlue::COMMA_LIST,
        );

        if !generics.is_empty() {
            write!(f, "<{generics}>")?;
        }

        Ok(())
    }
    Obj<Item> => |cx, value, f| {
        let s = cx.session();
        f.write_str(value.r(s).path.as_str(s))
    }
    InferTyVar => |cx, value, f| {
        match cx.ccx.lookup_ty_infer_var_without_poll(value) {
            Ok(resolved) => cx.wrap(resolved).fmt(f),
            Err(root) => {
                if cx.opts.verbose {
                    write!(f, "?(level = {}) {}", root.max_universe.level(), root.root.index())
                } else {
                    // TODO
                    write!(f, "?{}", root.root.index())
                }
            },
        }
    }
    SimpleTySet => |cx, value, f| {
        format_list_into(f, value.names(), SimpleListFormatGlue::PIPE_LIST)
    }
    UniversalTy => |cx, value, f| {
        match value {
            UniversalTy::Root(var) => cx.wrap(var).fmt(f),
            UniversalTy::Projection(projection) => cx.wrap(projection).fmt(f),
        }
    }
    UniversalTyRoot => |cx, value, f| {
        let s = cx.session();

        if cx.opts.verbose {
            let universe = cx.ccx().lookup_universal_ty_hrtb_universe(UniversalTy::Root(value));

            write!(f, "u(level = {}) ", universe.level())?;
        }

        match cx.ccx().lookup_universal_ty_root_src_info(value) {
            UniversalTyVarSourceInfo::TraitSelf => write!(f, "Self"),
            UniversalTyVarSourceInfo::HrtbVar(name) => write!(f, "{name}"),
            UniversalTyVarSourceInfo::ClauseWfHelper { clauses } => {
                // TODO
                write!(f, "[clause WF helper]")
            },
            UniversalTyVarSourceInfo::HrtbWf { binder, idx } => {
                write!(f, "{}", binder.defs.r(s)[idx as usize].name)
            },
            UniversalTyVarSourceInfo::Root(generic) => write!(f, "{}", generic.r(s).ident.text),
        }
    }
    UniversalTyProj => |cx, value, f| {
        let s = cx.session();

        let HrtbProjection {
            target,
            spec,
            assoc_idx,
        } = cx.ccx().lookup_universal_ty_proj_debug_spec(value);

        write!(
            f,
            "<{} as {}>::{}",
            cx.wrap(target),
            cx.wrap(spec),
            spec.def.r(s).generics.r(s).defs[assoc_idx as usize].ident(s).text(),
        )
    }
    FnInstance => |cx, value, f| {
        let s = cx.session();

        f.write_str("fn @ ")?;

        match value.r(s).owner {
            FnOwner::Item(def) => {
                write!(f, "{}", cx.wrap(def.r(s).item))?;
            },
            FnOwner::Trait(FnOwnerTrait { instance, self_ty, method_idx }) => {
                write!(
                    f,
                    "<{} as {}>::{}",
                    cx.wrap(self_ty),
                    cx.wrap(instance),
                    instance.def.r(s).methods[method_idx as usize].r(s).name.text,
                )?;
            },
            FnOwner::Inherent(FnOwnerInherent { self_ty, block, method_idx }) => {
                write!(
                    f,
                    "<{}>::{}",
                    cx.wrap(self_ty),
                    block.r(s).methods[method_idx as usize].unwrap().r(s).name.text,
                )?;
            },
            FnOwner::AdtCtor(FnOwnerAdtCtor { ctor }) => {
                match ctor.r(s).owner {
                    AdtCtorOwner::Struct(def) => {
                        write!(f, "{}", cx.wrap(def.r(s).adt.r(s).item))?;
                    },
                    AdtCtorOwner::EnumVariant(def) => {
                        write!(
                            f,
                            "{}::{}",
                            cx.wrap(def.r(s).owner.r(s).adt.r(s).item),
                            def.r(s).ident.text,
                        )?;
                    },
                }
            },
        }

        if let Some(early) = value.r(s).early_args && !early.r(s).is_empty() {
            f.write_char('<')?;
            format_list_into(
                f,
                early.r(s).iter().map(|def| cx.wrap(def)),
                SimpleListFormatGlue::COMMA_LIST,
            )?;
            f.write_char('>')?;
        }

        Ok(())
    }
}

fn fmt_simple_ctor(cx: &PrettyFmtCx, def: Obj<Item>, args: TyOrReList) -> String {
    let s = cx.session();

    if args.r(s).is_empty() {
        cx.wrap(def).to_string()
    } else {
        format!(
            "{}<{}>",
            cx.wrap(def),
            format_list(
                args.r(s).iter().map(|value| cx.wrap(value)),
                SimpleListFormatGlue::COMMA_LIST,
            ),
        )
    }
}
