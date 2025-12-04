use crate::{
    base::{
        Diag, ErrorGuaranteed, LeafDiag,
        analysis::SpannedViewEncode as _,
        arena::Obj,
        syntax::{HasSpan as _, Span},
    },
    parse::{
        ast::{
            AstExprPath, AstExprPathKind, AstParamedPath, AstParamedPathSegment, AstPathPartKw,
            AstTyKind,
        },
        token::Ident,
    },
    semantic::{
        lower::{
            entry::IntraItemLowerCtxt,
            modules::{FrozenModuleResolver, ParentResolver, PathResolver, StepResolveError},
        },
        syntax::{
            AdtDef, EnumVariantItem, FnItem, FuncLocal, ItemKind, SpannedAdtInstanceView,
            SpannedTraitInstance, SpannedTraitInstanceView, SpannedTy, SpannedTyOrReList,
            SpannedTyView, TraitDef,
        },
    },
};

#[derive(Debug, Clone)]
pub enum ExprPathResolution {
    /// A reference to the `Self` type by itself.
    ResolvedSelfTy,

    /// A reference to some resolved ADT with some optional generic parameters.
    ResolvedAdt(Obj<AdtDef>, SpannedTyOrReList),

    /// A reference to some resolved enum variant with some optional generic parameters.
    ResolvedEnumVariant(Obj<EnumVariantItem>, SpannedTyOrReList),

    /// A reference to a function item with some optional generic parameters.
    ResolvedFn(Obj<FnItem>, SpannedTyOrReList),

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
    ///     - `self_ty = ExplicitInfer`
    ///     - `as_trait = Some(MyTrait<_>)`
    ///     - `assoc_name = foo`
    ///     - `assoc_args = None`
    /// - `MyTrait::<u32>::foo`:
    ///     - `self_ty = ExplicitInfer`
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

impl IntraItemLowerCtxt<'_> {
    pub fn resolve_expr_path(
        &mut self,
        path: &AstExprPath,
    ) -> Result<ExprPathResolution, ErrorGuaranteed> {
        match &path.kind {
            AstExprPathKind::Bare(path) => self.resolve_bare_expr_path(path),
            AstExprPathKind::SelfTy(_self_kw, None) => Ok(ExprPathResolution::ResolvedSelfTy),
            AstExprPathKind::SelfTy(self_kw, Some(rest)) => Ok(ExprPathResolution::TypeRelative {
                self_ty: SpannedTyView::This.encode(*self_kw, self.tcx),
                as_trait: None,
                assoc: self
                    .lower_rest_as_type_relative_assoc(self_kw.shrink_to_hi(), &rest.segments)?,
            }),
            AstExprPathKind::Qualified(qual, rest) => Ok(ExprPathResolution::TypeRelative {
                self_ty: self.lower_ty(&qual.self_ty),
                as_trait: qual.as_trait.as_ref().and_then(|for_trait| {
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
                }),
                assoc: self
                    .lower_rest_as_type_relative_assoc(qual.span.shrink_to_hi(), &rest.segments)?,
            }),
            AstExprPathKind::Error(err) => Err(*err),
        }
    }

    pub fn resolve_bare_expr_path(
        &mut self,
        path: &AstParamedPath,
    ) -> Result<ExprPathResolution, ErrorGuaranteed> {
        let s = &self.tcx.session;

        // See whether we can resolve this as a `self` or as a function local.
        if let Some(first) = &path.segments.first()
            && let Some(ident) = first.part.ident()
            && let Some(local) = self.func_local_names.lookup(ident.text)
        {
            if let Some(args) = &first.args {
                Diag::span_err(
                    args.span,
                    "local variables cannot be instantiated with generic parameters",
                )
                .emit();
            }

            if let Some(subsequent) = &path.segments.get(1) {
                Diag::span_err(
                    subsequent.part.span(),
                    "local variables cannot be accessed like modules",
                )
                .emit();
            }

            return Ok(ExprPathResolution::Local(*local));
        }

        if let [first] = &path.segments[..]
            && first.part.keyword() == Some(AstPathPartKw::Self_)
        {
            if let Some(args) = &first.args {
                Diag::span_err(
                    args.span,
                    "`self` cannot be instantiated with generic parameters",
                )
                .emit();
            }

            return Ok(ExprPathResolution::SelfLocal);
        }

        // Otherwise, let's resolve a path.
        let mut finger = self.scope;
        let mut resolver = FrozenModuleResolver(s);
        let mut segments = path.segments.iter();

        while let Some(segment) = segments.next() {
            match resolver.resolve_step(self.root, self.scope, finger, segment.part) {
                Ok(target) => finger = target,
                Err(err) => {
                    return Err(err.emit(&resolver, finger, segment.part));
                }
            }

            match *finger.r(s).kind {
                ItemKind::Module(_) | ItemKind::Impl(_) => {
                    // (fallthrough)
                }
                ItemKind::EnumVariant(variant) => {
                    return Ok(self.resolve_bare_expr_path_from_enum_variant(
                        variant,
                        None,
                        segment,
                        segments.as_slice(),
                    ));
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
                        "{} at `{}` does not accept generic parameters",
                        resolver.categorize(finger).a_what(),
                        resolver.path(finger),
                    ),
                )
                .emit();

                // (fallthrough)
            }
        }

        Err(Diag::span_err(
            path.span,
            format_args!(
                "path expressions cannot refer to {} `{}`",
                resolver.categorize(finger).bare_what(),
                resolver.path(finger),
            ),
        )
        .emit())
    }

    pub fn resolve_bare_expr_path_from_adt(
        &mut self,
        adt: Obj<AdtDef>,
        adt_segment: &AstParamedPathSegment,
        additional_segments: &[AstParamedPathSegment],
    ) -> Result<ExprPathResolution, ErrorGuaranteed> {
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
                    let variant = variant.r(s).kind.as_enum_variant().unwrap();

                    Ok(self.resolve_bare_expr_path_from_enum_variant(
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

                    let assoc =
                        self.lower_rest_as_type_relative_assoc(Span::DUMMY, additional_segments)?;

                    Ok(ExprPathResolution::TypeRelative {
                        self_ty,
                        as_trait: None,
                        assoc,
                    })
                }
                Err(err) => Err(err.emit(&resolver, adt.r(s).item, first_additional.part)),
            }
        } else {
            let generics = first_generics.unwrap_or_else(|| {
                self.synthesize_inferred_generics_for_elision(
                    adt.r(s).generics,
                    None,
                    adt_segment.part.span(),
                )
            });

            Ok(ExprPathResolution::ResolvedAdt(adt, generics))
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

        let adt = variant.r(s).owner.r(s).kind.as_adt().unwrap();

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
                second_generics.own_span().unwrap_or(Span::DUMMY),
                "generic parameters for `enum` specified more than once",
            )
            .child(LeafDiag::span_note(
                first_generics.own_span().unwrap_or(Span::DUMMY),
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
        def: Obj<TraitDef>,
        def_segment: &AstParamedPathSegment,
        segments: &[AstParamedPathSegment],
    ) -> Result<ExprPathResolution, ErrorGuaranteed> {
        let self_ty = SpannedTyView::ExplicitInfer.encode(def_segment.part.span(), self.tcx);

        let as_trait_generics = self.lower_generics_of_trait_instance_in_fn_body(
            def,
            def_segment.part.span(),
            def_segment.args.as_deref(),
        );

        let assoc = self
            .lower_rest_as_type_relative_assoc(def_segment.part.span().shrink_to_hi(), segments)?;

        Ok(ExprPathResolution::TypeRelative {
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
        def: Obj<FnItem>,
        def_segment: &AstParamedPathSegment,
        segments: &[AstParamedPathSegment],
    ) -> Result<ExprPathResolution, ErrorGuaranteed> {
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

        Ok(ExprPathResolution::ResolvedFn(def, generics))
    }

    pub fn lower_rest_as_type_relative_assoc(
        &mut self,
        missing_segment_span: Span,
        rest: &[AstParamedPathSegment],
    ) -> Result<TypeRelativeAssoc, ErrorGuaranteed> {
        let segment = match rest {
            [] => {
                return Err(Diag::span_err(
                    missing_segment_span,
                    "expected method or constant name",
                )
                .emit());
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

        let name = match segment.part.ident() {
            Some(name) => name,
            None => {
                return Err(Diag::span_err(
                    segment.part.span(),
                    "expected method or constant name",
                )
                .emit());
            }
        };

        Ok(TypeRelativeAssoc {
            name,
            args: self.lower_type_relative_generics(segment.args.as_deref()),
        })
    }
}
