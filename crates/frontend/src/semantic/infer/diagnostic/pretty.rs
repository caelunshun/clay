use crate::{
    base::{Session, analysis::DebruijnMap, arena::Obj, syntax::Symbol},
    semantic::{
        infer::ClauseCx,
        syntax::{
            AdtCtor, AdtCtorOwner, AdtInstance, FloatKind, FnInstance, FnOwner, HrtbBinder,
            HrtbDebruijn, HrtbDebruijnDef, HrtbProjection, InferReVar, InferTyVar,
            InferTyVarSourceInfo, IntKind, Item, Re, SimpleTyKind, SimpleTySet, TraitClause,
            TraitClauseList, TraitParam, TraitSpec, Ty, TyCtxt, TyKind, TyOrRe, TyOrReList,
            UniversalReVar, UniversalReVarSourceInfo, UniversalTy, UniversalTyProj,
            UniversalTyProjInner, UniversalTyRoot, UniversalTyRootSourceInfo,
        },
    },
    utils::format::{SimpleListFormatGlue, format_list, format_list_into},
};
use std::{
    cell::RefCell,
    fmt::{self, Write},
};

// === PrettyFmtCx === //

impl<'tcx> ClauseCx<'tcx> {
    pub fn pretty(&self, opts: ClausePrettyFmtOpts) -> ClausePrettyFmtCx<'_, 'tcx> {
        ClausePrettyFmtCx::new(self, opts)
    }
}

pub struct ClausePrettyFmtCx<'a, 'tcx> {
    ccx: &'a ClauseCx<'tcx>,
    opts: ClausePrettyFmtOpts,
    fmt_state: RefCell<FmtState>,
}

#[derive(Debug, Clone, Default)]
pub struct ClausePrettyFmtOpts {
    pub verbose: bool,
}

#[derive(Default)]
struct FmtState {
    hrtb_defs: DebruijnMap<Symbol>,
}

impl<'a, 'tcx> ClausePrettyFmtCx<'a, 'tcx> {
    pub fn new(ccx: &'a ClauseCx<'tcx>, opts: ClausePrettyFmtOpts) -> Self {
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

    pub fn wrap<T>(&self, value: T) -> ClausePrettyFmt<'_, 'tcx, T> {
        ClausePrettyFmt { cx: self, value }
    }
}

// === PrettyFmt === //

pub struct ClausePrettyFmt<'a, 'tcx, T> {
    pub cx: &'a ClausePrettyFmtCx<'a, 'tcx>,
    pub value: T,
}

impl<'a, 'tcx, T: Copy> fmt::Display for ClausePrettyFmt<'a, 'tcx, &'a T>
where
    ClausePrettyFmt<'a, 'tcx, T>: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.cx.wrap(*self.value).fmt(f)
    }
}

impl fmt::Display for ClausePrettyFmt<'_, '_, TyOrRe> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            TyOrRe::Re(re) => self.cx.wrap(re).fmt(f),
            TyOrRe::Ty(ty) => self.cx.wrap(ty).fmt(f),
        }
    }
}

impl fmt::Display for ClausePrettyFmt<'_, '_, Re> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO
        match self.value {
            Re::Gc => f.write_str("'gc"),
            Re::HrtbVar(debruijn) => write!(f, "'{}", self.cx.wrap(debruijn)),
            Re::InferVar(infer) => {
                if infer != InferReVar::ERASED {
                    write!(f, "'?{}", infer.index())
                } else {
                    write!(f, "'erased")
                }
            }
            Re::UniversalVar(re) => self.cx.wrap(re).fmt(f),
            Re::Error(_) => f.write_str("'error"),
        }
    }
}

impl fmt::Display for ClausePrettyFmt<'_, '_, UniversalReVar> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = self.cx.session();

        match self.cx.ccx().lookup_universal_re_src_info(self.value) {
            UniversalReVarSourceInfo::Root(re) => {
                write!(f, "'{}", re.r(s).lifetime.name)
            }
            // TODO
            UniversalReVarSourceInfo::ElaboratedLub
            | UniversalReVarSourceInfo::InstantiatedHrtbVar
            | UniversalReVarSourceInfo::HrtbWf { .. }
            | UniversalReVarSourceInfo::MirLocal(..) => {
                write!(f, "'u{}", self.value.index())
            }
        }
    }
}

impl fmt::Display for ClausePrettyFmt<'_, '_, Ty> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = self.cx.session();

        match *self.value.r(s) {
            TyKind::Simple(kind) => self.cx.wrap(kind).fmt(f),
            TyKind::Reference(lt, muta, pointee) => {
                write!(
                    f,
                    "&{} {}{}",
                    self.cx.wrap(lt),
                    muta.opt_space_qual(),
                    self.cx.wrap(pointee)
                )
            }
            TyKind::Adt(instance) => self.cx.wrap(instance).fmt(f),
            TyKind::Trait(lt, muta, clauses) => {
                write!(
                    f,
                    "&{} {}dyn {}",
                    self.cx.wrap(lt),
                    muta.opt_space_qual(),
                    self.cx.wrap(clauses)
                )
            }
            TyKind::Tuple(types) => {
                if let [unique] = types.r(s) {
                    write!(f, "({},)", self.cx.wrap(unique))
                } else {
                    write!(
                        f,
                        "({})",
                        format_list(
                            types.r(s).iter().map(|value| self.cx.wrap(value)),
                            SimpleListFormatGlue::COMMA_LIST,
                        ),
                    )
                }
            }
            TyKind::FnDef(def) => self.cx.wrap(def).fmt(f),
            TyKind::HrtbVar(var) => self.cx.wrap(var).fmt(f),
            TyKind::HrtbProjection(HrtbProjection {
                target,
                spec,
                assoc_idx,
            }) => {
                write!(
                    f,
                    "<{} as {}>::{}",
                    self.cx.wrap(target),
                    self.cx.wrap(spec),
                    spec.def.r(s).generics.r(s).defs[assoc_idx as usize]
                        .ident(s)
                        .text(),
                )
            }
            TyKind::InferVar(var) => self.cx.wrap(var).fmt(f),
            TyKind::Universal(var) => self.cx.wrap(var).fmt(f),
            TyKind::Error(_) => f.write_str("<error>"),
        }
    }
}

impl fmt::Display for ClausePrettyFmt<'_, '_, SimpleTyKind> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self.value {
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
}

impl fmt::Display for ClausePrettyFmt<'_, '_, AdtInstance> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = self.cx.session();
        let AdtInstance { def, params } = self.value;
        f.write_str(&fmt_simple_ctor(self.cx, def.r(s).item, params))
    }
}

impl fmt::Display for ClausePrettyFmt<'_, '_, TraitClauseList> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = self.cx.session();
        format_list_into(
            f,
            self.value.r(s).iter().map(|clause| self.cx.wrap(clause)),
            SimpleListFormatGlue::PLUS_LIST,
        )
    }
}
impl fmt::Display for ClausePrettyFmt<'_, '_, TraitClause> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            TraitClause::Outlives(dir, other) => {
                write!(f, "{} {}", dir.kw(), self.cx.wrap(other))
            }
            TraitClause::Trait(binder) => self.cx.wrap(binder).fmt(f),
        }
    }
}

impl fmt::Display for ClausePrettyFmt<'_, '_, HrtbBinder> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = self.cx.session();
        let HrtbBinder { defs, inner } = self.value;

        if !defs.r(s).is_empty() {
            f.write_str("for<")?;
            format_list_into(
                f,
                defs.r(s).iter().map(|def| self.cx.wrap(def)),
                SimpleListFormatGlue::COMMA_LIST,
            )?;
            f.write_str("> ")?;
        }

        let count = self
            .cx
            .fmt_state
            .borrow_mut()
            .hrtb_defs
            .push(defs.r(s).iter().map(|v| v.name));

        self.cx.wrap(inner).fmt(f)?;
        self.cx.fmt_state.borrow_mut().hrtb_defs.pop(count);

        Ok(())
    }
}

impl fmt::Display for ClausePrettyFmt<'_, '_, HrtbDebruijnDef> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = self.cx.session();
        let HrtbDebruijnDef {
            span: _,
            name,
            kind: _,
            clauses,
        } = self.value;

        f.write_str(name.as_str(s))?;

        if clauses.r(s).is_empty() {
            return Ok(());
        }

        write!(f, ": {}", self.cx.wrap(clauses))?;
        Ok(())
    }
}

impl fmt::Display for ClausePrettyFmt<'_, '_, HrtbDebruijn> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self
            .cx
            .fmt_state
            .borrow()
            .hrtb_defs
            .try_lookup(self.value.0)
        {
            Some(name) => name.fmt(f),
            None => write!(f, "debruijn({})", self.value.0.idx()),
        }
    }
}

impl fmt::Display for ClausePrettyFmt<'_, '_, TraitSpec> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = self.cx.session();
        let TraitSpec { def, params } = self.value;
        self.cx.wrap(def.r(s).item).fmt(f)?;
        let generics = format_list(
            params
                .r(s)
                .iter()
                .enumerate()
                .filter_map(|(def_idx, para)| {
                    if def_idx < *def.r(s).regular_generic_count as usize {
                        let TraitParam::Equals(para) = *para else {
                            unreachable!()
                        };
                        return Some(self.cx.wrap(para).to_string());
                    }
                    let name = def.r(s).generics.r(s).defs[def_idx].ident(s).text();
                    match para {
                        TraitParam::Equals(para) => {
                            Some(format!("{name} = {}", self.cx.wrap(para)))
                        }
                        TraitParam::Unspecified(clauses) => {
                            if !clauses.r(s).is_empty() {
                                Some(format!("{name}: {}", self.cx.wrap(clauses)))
                            } else {
                                None
                            }
                        }
                    }
                }),
            SimpleListFormatGlue::COMMA_LIST,
        );
        if !generics.is_empty() {
            write!(f, "<{generics}>")?;
        }
        Ok(())
    }
}

impl fmt::Display for ClausePrettyFmt<'_, '_, Obj<Item>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = self.cx.session();
        f.write_str(self.value.r(s).path.as_str(s))
    }
}

impl fmt::Display for ClausePrettyFmt<'_, '_, Obj<AdtCtor>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = self.cx.session();
        f.write_str(&self.value.r(s).owner.bare_identified_what(s))
    }
}

impl fmt::Display for ClausePrettyFmt<'_, '_, InferTyVar> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = self.cx.session();
        match self.cx.ccx().lookup_ty_infer_var_without_poll(self.value) {
            Ok(resolved) => self.cx.wrap(resolved).fmt(f),
            Err(root) => {
                if self.cx.opts.verbose {
                    write!(f, "?({:?}) ", root.root)?;
                }
                match self.cx.ccx().lookup_infer_ty_src_info(root.root) {
                    InferTyVarSourceInfo::Projection { self_ty, spec, idx } => {
                        write!(
                            f,
                            "<{} as {}>::{}",
                            self.cx.wrap(self_ty),
                            self.cx.wrap(spec),
                            spec.def.r(s).generics.r(s).defs[idx as usize]
                                .ident(s)
                                .text(),
                        )?;
                    }
                    InferTyVarSourceInfo::LateAssocElabPlaceholder
                    | InferTyVarSourceInfo::HrtbLhsInstantiation { .. }
                    | InferTyVarSourceInfo::DirectlyImported { .. }
                    | InferTyVarSourceInfo::TraitParam { .. }
                    | InferTyVarSourceInfo::ImplBlockParam { .. }
                    | InferTyVarSourceInfo::LateBoundFnGeneric { .. }
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
                    | InferTyVarSourceInfo::MethodLookupHelper => {
                        write!(f, "_")?;
                    }
                }
                Ok(())
            }
        }
    }
}

impl fmt::Display for ClausePrettyFmt<'_, '_, SimpleTySet> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        format_list_into(f, self.value.names(), SimpleListFormatGlue::PIPE_LIST)
    }
}

impl fmt::Display for ClausePrettyFmt<'_, '_, UniversalTy> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            UniversalTy::Root(var) => self.cx.wrap(var).fmt(f),
            UniversalTy::Projection(projection) => self.cx.wrap(projection).fmt(f),
        }
    }
}

impl fmt::Display for ClausePrettyFmt<'_, '_, UniversalTyRoot> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = self.cx.session();
        if self.cx.opts.verbose {
            write!(f, "u({}) ", self.value.index())?;
        }
        match self.cx.ccx().lookup_universal_ty_root_src_info(self.value) {
            UniversalTyRootSourceInfo::Root(generic) => write!(f, "{}", generic.r(s).ident.text),
            UniversalTyRootSourceInfo::UsedDyn { span, site } => write!(
                f,
                "existential #{site:?} (dyn {clauses} from {span})",
                clauses =
                    self.cx
                        .wrap(self.cx.ccx().direct_ty_universal_clauses_possibly_floating(
                            UniversalTy::Root(self.value)
                        ),),
            ),
            UniversalTyRootSourceInfo::InstantiatedHrtb(name) => write!(f, "{name}"),
            UniversalTyRootSourceInfo::WfTraitSelf => write!(f, "Self"),
            UniversalTyRootSourceInfo::WfReflexive { clauses: _ } => {
                write!(f, "[clause WF helper]")
            }
            UniversalTyRootSourceInfo::WfHrtbUniversal { binder, idx } => {
                write!(f, "{}", binder.defs.r(s)[idx as usize].name)
            }
        }
    }
}

impl fmt::Display for ClausePrettyFmt<'_, '_, UniversalTyProj> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = self.cx.session();
        let UniversalTyProjInner {
            target,
            as_spec,
            assoc_idx,
            cache_idx,
        } = *self.value.r(s);
        if self.cx.opts.verbose {
            write!(f, "u({cache_idx:?}) ")?;
        }
        write!(
            f,
            "<{} as {}>::{}",
            self.cx.wrap(target),
            self.cx.wrap(as_spec),
            as_spec.def.r(s).generics.r(s).defs[assoc_idx as usize]
                .ident(s)
                .text(),
        )
    }
}

impl fmt::Display for ClausePrettyFmt<'_, '_, FnInstance> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = self.cx.session();
        f.write_str("fn @ ")?;
        match self.value.r(s).owner {
            FnOwner::Item(def) => {
                write!(f, "{}", self.cx.wrap(def.r(s).item))?;
            }
            FnOwner::Trait {
                instance,
                self_ty,
                method_idx,
            } => {
                write!(
                    f,
                    "<{} as {}>::{}",
                    self.cx.wrap(self_ty),
                    self.cx.wrap(instance),
                    instance.def.r(s).methods[method_idx as usize]
                        .r(s)
                        .name
                        .text,
                )?;
            }
            FnOwner::Inherent {
                self_ty,
                block,
                method_idx,
            } => {
                write!(
                    f,
                    "<{}>::{}",
                    self.cx.wrap(self_ty),
                    block.r(s).methods[method_idx as usize]
                        .unwrap()
                        .r(s)
                        .name
                        .text,
                )?;
            }
            FnOwner::AdtCtor(ctor) => match ctor.r(s).owner {
                AdtCtorOwner::Struct(def) => {
                    write!(f, "{}", self.cx.wrap(def.r(s).adt.r(s).item))?;
                }
                AdtCtorOwner::EnumVariant(def) => {
                    write!(
                        f,
                        "{}::{}",
                        self.cx.wrap(def.r(s).owner.r(s).adt.r(s).item),
                        def.r(s).ident.text,
                    )?;
                }
            },
        }
        if let Some(early) = self.value.r(s).early_args
            && !early.r(s).is_empty()
        {
            f.write_char('<')?;
            format_list_into(
                f,
                early.r(s).iter().map(|def| self.cx.wrap(def)),
                SimpleListFormatGlue::COMMA_LIST,
            )?;
            f.write_char('>')?;
        }
        Ok(())
    }
}

fn fmt_simple_ctor(cx: &ClausePrettyFmtCx, def: Obj<Item>, args: TyOrReList) -> String {
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
