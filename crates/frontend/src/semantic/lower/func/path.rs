use crate::{
    base::{
        Diag, ErrorGuaranteed, LeafDiag, Session, analysis::SpannedViewEncode as _, arena::Obj,
        syntax::HasSpan as _,
    },
    parse::{
        ast::{
            AstExprPath, AstExprPathKind, AstParamedPath, AstParamedPathSegment, AstPathPartKind,
            AstPathPartKw, AstTyKind,
        },
        token::Ident,
    },
    semantic::{
        lower::{
            entry::IntraItemLowerCtxt,
            modules::{FrozenModuleResolver, PathResolver, StepResolveError},
        },
        syntax::{
            AdtCtorInstance, AdtItem, AdtKind, EnumVariantItem, FuncItem, FuncLocal, Item,
            ItemKind, SpannedAdtInstanceView, SpannedTraitInstance, SpannedTraitInstanceView,
            SpannedTy, SpannedTyOrReList, SpannedTyView, TraitItem, TypeGeneric,
        },
    },
};

// === Result Definition === //

#[derive(Debug, Copy, Clone)]
pub enum ExprPathResult {
    Resolved(ExprPathResolution),
    UnboundLocal(Ident),
    Fail(ErrorGuaranteed),
}

#[derive(Debug, Copy, Clone)]
pub enum ExprPathResolution {
    /// A reference to the `Self` type by itself.
    ResolvedSelfTy,

    /// A reference to a module or perhaps a scope.
    ResolvedModule(Obj<Item>),

    /// A reference to some resolved ADT with some optional generic parameters.
    ResolvedAdt(Obj<AdtItem>, SpannedTyOrReList),

    /// A reference to some resolved enum variant with some optional generic parameters.
    ResolvedEnumVariant(Obj<EnumVariantItem>, SpannedTyOrReList),

    /// A reference to a function item with some optional generic parameters.
    ResolvedFn(Obj<FuncItem>, SpannedTyOrReList),

    /// A reference to a trait.
    ResolvedTrait(Obj<TraitItem>, SpannedTyOrReList),

    /// A reference to a generic type.
    ResolvedGeneric(Obj<TypeGeneric>),

    /// A reference to a type with some further qualifications for methods or constants that cannot
    /// be solved at lowering time. Note that types without further qualifications will be treated
    /// as `Resolved` or `ResolvedSelfTy` to maintain exactly one representation for such scenarios.
    ///
    /// For example...
    ///
    /// - `Self::new`:
    ///     - `self_ty = This`
    ///     - `as_trait = None`
    ///     - `assoc_name = new`
    ///     - `assoc_args = None`
    /// - `Self::new::<u32>`:
    ///     - `self_ty = This`
    ///     - `as_trait = None`
    ///     - `assoc_name = new`
    ///     - `assoc_args = Some([u32])`
    /// - `<()>::woo`:
    ///     - `self_ty = ()`
    ///     - `as_trait = None`
    ///     - `assoc_name = woo`
    ///     - `assoc_args = None`
    /// - `T::new`:
    ///     - `self_ty = Universal(T)`
    ///     - `as_trait = None`
    ///     - `assoc_name = new`
    ///     - `assoc_args = None`
    /// - `MyTrait::foo`:
    ///     - `self_ty = SigInfer`
    ///     - `as_trait = Some(MyTrait<_>)`
    ///     - `assoc_name = foo`
    ///     - `assoc_args = None`
    /// - `MyTrait::<u32>::foo`:
    ///     - `self_ty = SigInfer`
    ///     - `as_trait = Some(MyTrait<u32>)`
    ///     - `assoc_name = foo`
    ///     - `assoc_args = None`
    ///
    TypeRelative {
        self_ty: SpannedTy,
        as_trait: Option<SpannedTraitInstance>,
        assoc: TypeRelativeAssoc,
    },

    /// The regular `self` keyword, which refers to a local.
    SelfLocal,

    /// A reference to a local defined within the current function.
    Local(Obj<FuncLocal>),
}

#[derive(Debug, Copy, Clone)]
pub struct TypeRelativeAssoc {
    pub name: Ident,
    pub args: Option<SpannedTyOrReList>,
}

impl ExprPathResult {
    pub fn fail_on_unbound_local(self) -> Result<ExprPathResolution, ErrorGuaranteed> {
        match self {
            ExprPathResult::Resolved(res) => Ok(res),
            ExprPathResult::UnboundLocal(ident) => Err(Diag::span_err(
                ident.span,
                format_args!("`{}` not found in scope", ident.text),
            )
            .emit()),
            ExprPathResult::Fail(err) => Err(err),
        }
    }

    pub fn as_ident_or_res(
        self,
        path: &AstExprPath,
        s: &Session,
    ) -> Result<ExprPathIdentOrResolution, ErrorGuaranteed> {
        match self {
            ExprPathResult::Resolved(res) => {
                if let ExprPathResolution::Local(def) = res {
                    Ok(ExprPathIdentOrResolution::Ident(Ident {
                        span: path.span,
                        text: def.r(s).name.text,
                        raw: false,
                    }))
                } else {
                    Ok(ExprPathIdentOrResolution::Resolution(res))
                }
            }
            ExprPathResult::UnboundLocal(ident) => Ok(ExprPathIdentOrResolution::Ident(ident)),
            ExprPathResult::Fail(err) => Err(err),
        }
    }
}

impl ExprPathResolution {
    pub fn bare_what(self, s: &Session) -> String {
        match self {
            ExprPathResolution::ResolvedSelfTy => "`Self`".to_string(),
            ExprPathResolution::ResolvedModule(def) => def.r(s).bare_category_path(s),
            ExprPathResolution::ResolvedAdt(def, _) => def.r(s).item.r(s).bare_category_path(s),
            ExprPathResolution::ResolvedEnumVariant(def, _) => {
                def.r(s).item.r(s).bare_category_path(s)
            }
            ExprPathResolution::ResolvedFn(def, _) => def.r(s).item.r(s).bare_category_path(s),
            ExprPathResolution::ResolvedTrait(def, _) => def.r(s).item.r(s).bare_category_path(s),
            ExprPathResolution::ResolvedGeneric(def) => {
                format!("generic type `{}`", def.r(s).ident.text)
            }
            ExprPathResolution::TypeRelative { .. } => {
                "fully-qualified constant or method".to_string()
            }
            ExprPathResolution::SelfLocal => "`self`".to_string(),
            ExprPathResolution::Local(def) => format!("local variable `{}`", def.r(s).name.text),
        }
    }

    pub fn as_value(self, s: &Session) -> Option<PathResolvedValue> {
        if let Some(local) = self.as_local() {
            return Some(PathResolvedValue::Local(local));
        }

        if let Some(fn_lit) = self.as_fn_lit() {
            return Some(PathResolvedValue::FnLit(fn_lit));
        }

        if let Some(adt_ctor) = self.as_adt_ctor(s) {
            return Some(PathResolvedValue::AdtCtor(adt_ctor));
        }

        None
    }

    pub fn as_pat(self, s: &Session) -> Option<PathResolvedPattern> {
        if let Some(adt_ctor) = self.as_adt_ctor(s)
            && adt_ctor.def.r(s).syntax.is_unit()
        {
            return Some(PathResolvedPattern::UnitCtor(adt_ctor));
        }

        None
    }

    pub fn as_local(self) -> Option<PathResolvedLocal> {
        match self {
            ExprPathResolution::SelfLocal => Some(PathResolvedLocal::LowerSelf),
            ExprPathResolution::Local(local) => Some(PathResolvedLocal::Local(local)),
            _ => None,
        }
    }

    pub fn as_fn_lit(self) -> Option<PathResolvedFnLit> {
        match self {
            ExprPathResolution::TypeRelative {
                self_ty,
                as_trait,
                assoc,
            } => Some(PathResolvedFnLit::TypeRelative {
                self_ty,
                as_trait,
                assoc,
            }),
            ExprPathResolution::ResolvedFn(def, params) => {
                Some(PathResolvedFnLit::Item(def, params))
            }
            _ => None,
        }
    }

    pub fn as_adt_ctor(self, s: &Session) -> Option<AdtCtorInstance> {
        match self {
            ExprPathResolution::ResolvedSelfTy => todo!(),
            ExprPathResolution::ResolvedAdt(def, params) => match *def.r(s).kind {
                AdtKind::Struct(def) => Some(AdtCtorInstance {
                    def: *def.r(s).ctor,
                    params,
                }),
                AdtKind::Enum(_) => None,
            },
            ExprPathResolution::ResolvedEnumVariant(def, params) => Some(AdtCtorInstance {
                def: *def.r(s).adt_variant(s).r(s).ctor,
                params,
            }),
            _ => None,
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum ExprPathIdentOrResolution {
    Ident(Ident),
    Resolution(ExprPathResolution),
}

#[derive(Debug, Copy, Clone)]
pub enum PathResolvedPattern {
    UnitCtor(AdtCtorInstance),
}

#[derive(Debug, Copy, Clone)]
pub enum PathResolvedValue {
    Local(PathResolvedLocal),
    FnLit(PathResolvedFnLit),
    AdtCtor(AdtCtorInstance),
}

#[derive(Debug, Copy, Clone)]
pub enum PathResolvedLocal {
    Local(Obj<FuncLocal>),
    LowerSelf,
}

#[derive(Debug, Copy, Clone)]
pub enum PathResolvedFnLit {
    Item(Obj<FuncItem>, SpannedTyOrReList),
    TypeRelative {
        self_ty: SpannedTy,
        as_trait: Option<SpannedTraitInstance>,
        assoc: TypeRelativeAssoc,
    },
}

// === Resolution Routine === //

impl IntraItemLowerCtxt<'_> {
    pub fn resolve_expr_path(&mut self, path: &AstExprPath) -> ExprPathResult {
        match &path.kind {
            AstExprPathKind::Bare(path) => self.resolve_bare_expr_path(path),
            AstExprPathKind::SelfTy(_self_kw, None) => {
                ExprPathResult::Resolved(ExprPathResolution::ResolvedSelfTy)
            }
            AstExprPathKind::SelfTy(self_kw, Some(rest)) => {
                let assoc = match self.lower_rest_as_type_relative_assoc(&rest.segments) {
                    Ok(v) => v.unwrap(),
                    Err(err) => return ExprPathResult::Fail(err),
                };

                ExprPathResult::Resolved(ExprPathResolution::TypeRelative {
                    self_ty: SpannedTyView::SigThis.encode(*self_kw, self.tcx),
                    as_trait: None,
                    assoc,
                })
            }
            AstExprPathKind::Qualified(qual, rest) => {
                let self_ty = self.lower_ty(&qual.self_ty);

                let as_trait = qual.as_trait.as_ref().and_then(|for_trait| {
                    let AstTyKind::Name(path, params) = &for_trait.kind else {
                        Diag::span_err(for_trait.span, "expected a trait, found a type").emit();

                        return None;
                    };

                    let Ok(def) = self.resolve_ty_item_path_as_trait(path) else {
                        return None;
                    };

                    let params = self.lower_generics_of_trait_instance_in_fn_body(
                        def,
                        for_trait.span,
                        params.as_ref(),
                    );

                    Some(SpannedTraitInstanceView { def, params }.encode(for_trait.span, self.tcx))
                });

                let assoc = match self.lower_rest_as_type_relative_assoc(&rest.segments) {
                    Ok(v) => v.unwrap(),
                    Err(err) => return ExprPathResult::Fail(err),
                };

                ExprPathResult::Resolved(ExprPathResolution::TypeRelative {
                    self_ty,
                    as_trait,
                    assoc,
                })
            }
            AstExprPathKind::Error(err) => ExprPathResult::Fail(*err),
        }
    }

    pub fn resolve_bare_expr_path(&mut self, path: &AstParamedPath) -> ExprPathResult {
        let s = &self.tcx.session;

        // See whether we can resolve this as a `self` or as a function local.
        let local_like = if let [single_segment] = &path.segments[..]
            && let Some(ident) = single_segment.part.ident()
            && single_segment.args.is_none()
        {
            if let Some(local) = self.func_local_names.lookup(ident.text) {
                return ExprPathResult::Resolved(ExprPathResolution::Local(*local));
            }

            Some(ident)
        } else {
            None
        };

        if let [single_segment] = &path.segments[..]
            && single_segment.part.keyword() == Some(AstPathPartKw::Self_)
        {
            if let Some(args) = &single_segment.args {
                Diag::span_err(args.span, "type arguments are not allowed on `self`").emit();
            }

            return ExprPathResult::Resolved(ExprPathResolution::SelfLocal);
        }

        // See whether we're referring to a generic type.
        if let Some((first, subsequent)) = path.segments.split_first()
            && let Some(ident) = first.part.ident()
            && let Some(&generic) = self.generic_ty_names.lookup(ident.text)
        {
            if let Some(args) = &first.args {
                Diag::span_err(
                    args.span,
                    format_args!(
                        "type arguments are not allowed on generic type `{}`",
                        ident.text,
                    ),
                )
                .emit();
            }

            return match self.lower_rest_as_type_relative_assoc(subsequent) {
                Ok(Some(assoc)) => {
                    let self_ty = SpannedTyView::SigGeneric(generic).encode(ident.span, self.tcx);

                    ExprPathResult::Resolved(ExprPathResolution::TypeRelative {
                        self_ty,
                        as_trait: None,
                        assoc,
                    })
                }
                // Errors should fallback to a bare resolved generic.
                Ok(None) | Err(_) => {
                    ExprPathResult::Resolved(ExprPathResolution::ResolvedGeneric(generic))
                }
            };
        }

        // Otherwise, let's resolve a path.
        let mut finger = self.scope;
        let mut resolver = FrozenModuleResolver(s);
        let mut segments = path.segments.iter();

        while let Some(segment) = segments.next() {
            match resolver.resolve_step(self.root, self.scope, finger, segment.part) {
                Ok(target) => finger = target,
                Err(err @ StepResolveError::NotFound) => {
                    if let Some(local_like) = local_like {
                        return ExprPathResult::UnboundLocal(local_like);
                    } else {
                        return ExprPathResult::Fail(err.emit(&resolver, finger, segment.part));
                    }
                }
                Err(err) => {
                    return ExprPathResult::Fail(err.emit(&resolver, finger, segment.part));
                }
            }

            match *finger.r(s).kind {
                ItemKind::Module(_) | ItemKind::Impl(_) => {
                    // (fallthrough)
                }
                ItemKind::EnumVariant(variant) => {
                    return ExprPathResult::Resolved(
                        self.resolve_bare_expr_path_from_enum_variant(
                            variant,
                            None,
                            segment,
                            segments.as_slice(),
                        ),
                    );
                }
                ItemKind::Adt(adt) => {
                    return self.resolve_bare_expr_path_from_adt(adt, segment, segments.as_slice());
                }
                ItemKind::Trait(def) => {
                    return self.resolve_bare_expr_path_from_trait(
                        def,
                        segment,
                        segments.as_slice(),
                    );
                }
                ItemKind::Func(def) => {
                    return self.resolve_bare_expr_path_from_func(
                        def,
                        segment,
                        segments.as_slice(),
                    );
                }
            }

            if let Some(args) = &segment.args {
                Diag::span_err(
                    args.span,
                    format_args!(
                        "{} does not accept generic parameters",
                        finger.r(s).bare_category_path(s),
                    ),
                )
                .emit();

                // (fallthrough)
            }
        }

        ExprPathResult::Resolved(ExprPathResolution::ResolvedModule(finger))
    }

    pub fn resolve_bare_expr_path_from_adt(
        &mut self,
        adt: Obj<AdtItem>,
        adt_segment: &AstParamedPathSegment,
        additional_segments: &[AstParamedPathSegment],
    ) -> ExprPathResult {
        let s = &self.tcx.session;
        let mut resolver = FrozenModuleResolver(s);

        let first_generics = adt_segment.args.as_ref().map(|args| {
            self.lower_generics_of_entirely_positional(
                adt.r(s).item,
                adt.r(s).generics,
                args.span,
                &args.list,
            )
        });

        if let Some((first_additional, rest_additional)) = additional_segments.split_first() {
            match resolver.resolve_step(self.root, self.scope, adt.r(s).item, first_additional.part)
            {
                Ok(variant) => {
                    let variant = variant
                        .r(s)
                        .kind
                        .as_enum_variant()
                        // Unwrap OK: enums can only contain variants and we pre-validated the path
                        // to avoid path escapes.
                        .unwrap();

                    ExprPathResult::Resolved(self.resolve_bare_expr_path_from_enum_variant(
                        variant,
                        first_generics,
                        first_additional,
                        rest_additional,
                    ))
                }
                Err(StepResolveError::NotFound) => {
                    let self_ty = SpannedTyView::Adt(
                        SpannedAdtInstanceView {
                            def: adt,
                            params: first_generics.unwrap_or_else(|| {
                                self.synthesize_inferred_generics_for_elision(
                                    adt.r(s).generics,
                                    None,
                                    first_additional.part.span(),
                                )
                            }),
                        }
                        .encode(adt_segment.part.span(), self.tcx),
                    )
                    .encode(adt_segment.part.span(), self.tcx);

                    let assoc = match self.lower_rest_as_type_relative_assoc(additional_segments) {
                        // Unwrap OK: `additional_segments` is non-empty.
                        Ok(v) => v.unwrap(),
                        Err(err) => return ExprPathResult::Fail(err),
                    };

                    ExprPathResult::Resolved(ExprPathResolution::TypeRelative {
                        self_ty,
                        as_trait: None,
                        assoc,
                    })
                }
                Err(err) => {
                    ExprPathResult::Fail(err.emit(&resolver, adt.r(s).item, first_additional.part))
                }
            }
        } else {
            let generics = first_generics.unwrap_or_else(|| {
                self.synthesize_inferred_generics_for_elision(
                    adt.r(s).generics,
                    None,
                    adt_segment.part.span(),
                )
            });

            ExprPathResult::Resolved(ExprPathResolution::ResolvedAdt(adt, generics))
        }
    }

    pub fn resolve_bare_expr_path_from_enum_variant(
        &mut self,
        variant: Obj<EnumVariantItem>,
        first_generics: Option<SpannedTyOrReList>,
        variant_segment: &AstParamedPathSegment,
        additional_segments: &[AstParamedPathSegment],
    ) -> ExprPathResolution {
        let s = &self.tcx.session;
        let resolver = FrozenModuleResolver(s);

        if let Some(further) = additional_segments.first() {
            StepResolveError::NotFound.emit(&resolver, variant.r(s).item, further.part);
        }

        let adt = variant.r(s).adt(s);

        let second_generics = variant_segment.args.as_ref().map(|args| {
            self.lower_generics_of_entirely_positional(
                adt.r(s).item,
                adt.r(s).generics,
                args.span,
                &args.list,
            )
        });

        if let (Some(first_generics), Some(second_generics)) = (first_generics, second_generics) {
            Diag::span_err(
                second_generics.own_span(),
                "generic parameters for `enum` specified more than once",
            )
            .child(LeafDiag::span_note(
                first_generics.own_span(),
                "generics first specified here",
            ))
            .emit();
        }

        let generics = first_generics.or(second_generics).unwrap_or_else(|| {
            self.synthesize_inferred_generics_for_elision(
                adt.r(s).generics,
                None,
                variant_segment.part.span(),
            )
        });

        ExprPathResolution::ResolvedEnumVariant(variant, generics)
    }

    pub fn resolve_bare_expr_path_from_trait(
        &mut self,
        def: Obj<TraitItem>,
        def_segment: &AstParamedPathSegment,
        segments: &[AstParamedPathSegment],
    ) -> ExprPathResult {
        let as_trait_generics = self.lower_generics_of_trait_instance_in_fn_body(
            def,
            def_segment.part.span(),
            def_segment.args.as_deref(),
        );

        let Ok(Some(assoc)) = self.lower_rest_as_type_relative_assoc(segments) else {
            return ExprPathResult::Resolved(ExprPathResolution::ResolvedTrait(
                def,
                as_trait_generics,
            ));
        };

        let self_ty = SpannedTyView::SigInfer.encode(def_segment.part.span(), self.tcx);

        ExprPathResult::Resolved(ExprPathResolution::TypeRelative {
            self_ty,
            as_trait: Some(
                SpannedTraitInstanceView {
                    def,
                    params: as_trait_generics,
                }
                .encode(def_segment.part.span(), self.tcx),
            ),
            assoc,
        })
    }

    pub fn resolve_bare_expr_path_from_func(
        &mut self,
        def: Obj<FuncItem>,
        def_segment: &AstParamedPathSegment,
        segments: &[AstParamedPathSegment],
    ) -> ExprPathResult {
        let s = &self.tcx.session;

        if let Some(extra_segment) = segments.first() {
            Diag::span_err(
                extra_segment.part.span(),
                "function cannot be accessed like a module",
            )
            .emit();
        }

        let generics = def_segment
            .args
            .as_ref()
            .map(|args| {
                self.lower_generics_of_entirely_positional(
                    def.r(s).item,
                    def.r(s).def.r(s).generics,
                    args.span,
                    &args.list,
                )
            })
            .unwrap_or_else(|| {
                self.synthesize_inferred_generics_for_elision(
                    def.r(s).def.r(s).generics,
                    None,
                    def_segment.part.span(),
                )
            });

        ExprPathResult::Resolved(ExprPathResolution::ResolvedFn(def, generics))
    }

    pub fn lower_rest_as_type_relative_assoc(
        &mut self,
        rest: &[AstParamedPathSegment],
    ) -> Result<Option<TypeRelativeAssoc>, ErrorGuaranteed> {
        let segment = match rest {
            [] => {
                return Ok(None);
            }
            [segment] => segment,
            [segment, extra_segment, ..] => {
                Diag::span_err(
                    extra_segment.part.span(),
                    "method or constant cannot be accessed like a module",
                )
                .emit();

                segment
            }
        };

        let name = match segment.part.kind() {
            AstPathPartKind::Keyword(span, kw) => {
                return Err(Diag::span_err(
                    span,
                    format_args!(
                        "`{}` can only be applied to a module, not a type",
                        kw.kw().str()
                    ),
                )
                .emit());
            }
            AstPathPartKind::Regular(name) => name,
        };

        Ok(Some(TypeRelativeAssoc {
            name,
            args: self.lower_type_relative_generics(segment.args.as_deref()),
        }))
    }
}
