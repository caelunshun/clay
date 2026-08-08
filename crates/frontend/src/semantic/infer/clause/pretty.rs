use crate::{
    base::{Session, analysis::DebruijnTop, arena::Obj, syntax::Symbol},
    semantic::{
        infer::ClauseCx,
        syntax::{
            AdtInstance, FloatKind, HrtbBinder, HrtbDebruijnDef, InferTyVar, IntKind, Item, Re,
            SimpleTyKind, TraitClause, TraitClauseList, TraitParam, TraitSpec, Ty, TyCtxt, TyKind,
            TyOrRe, TyOrReList, UniversalTyVar,
        },
    },
    utils::lang::{SimpleListFormatGlue, format_list, format_list_into},
};
use std::{cell::RefCell, fmt};

// === PrettyFmtCx === //

impl<'tcx> ClauseCx<'tcx> {
    pub fn pretty(&self) -> PrettyFmtCx<'_, 'tcx> {
        PrettyFmtCx::new(self)
    }
}

pub struct PrettyFmtCx<'a, 'tcx> {
    ccx: &'a ClauseCx<'tcx>,
    fmt_state: RefCell<FmtState>,
}

#[derive(Default)]
struct FmtState {
    hrtb_top: DebruijnTop,
    hrtb_mappings: Vec<Symbol>,
}

impl<'a, 'tcx> PrettyFmtCx<'a, 'tcx> {
    pub fn new(ccx: &'a ClauseCx<'tcx>) -> Self {
        Self {
            ccx,
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
        write!(f, "'_")
    }
    Ty => |cx, value, f| {
        let s = cx.session();

        match *value.r(s) {
            TyKind::Simple(kind) => cx.wrap(kind).fmt(f),
            TyKind::Reference(lt, muta, pointee) => {
                write!(f, "&{} {}{}", cx.wrap(lt), muta.opt_space_qual(), cx.wrap(pointee))
            },
            TyKind::Adt(instance) => cx.wrap(instance).fmt(f),
            TyKind::Trait(re, muta, clauses) => todo!(),
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
            TyKind::FnDef(intern) => todo!(),
            TyKind::HrtbVar(var) => todo!(),
            TyKind::HrtbProjection(projection) => todo!(),
            TyKind::InferVar(var) => cx.wrap(var).fmt(f),
            TyKind::UniversalVar(var) => cx.wrap(var).fmt(f),
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

            f.write_str(">")?;
        }

        cx.wrap(inner).fmt(f)
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
    TraitSpec => |cx, value, f| {
        let s = cx.session();
        let TraitSpec { def, params } = value;

        cx.wrap(def.r(s).item).fmt(f)?;

        if params.r(s).is_empty() {
            return Ok(());
        }

        f.write_str("<")?;

        format_list_into(
            f,
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
        )?;

        f.write_str(">")?;

        Ok(())
    }
    Obj<Item> => |cx, value, f| {
        todo!()
    }
    InferTyVar => |cx, value, f| {
        write!(f, "{value:?}")
    }
    UniversalTyVar => |cx, value, f| {
        write!(f, "{value:?}")
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
