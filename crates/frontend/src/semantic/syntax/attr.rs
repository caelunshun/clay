use crate::{
    base::{
        Diag, ErrorGuaranteed, LeafDiag,
        arena::{LateInit, Obj},
        syntax::{Span, Symbol},
    },
    semantic::{
        analysis::TyCtxt,
        syntax::{Expr, Item, TraitItem},
    },
    symbol,
};
use std::fmt;

// === Attributes === //

#[derive(Debug, Clone)]
pub struct Attribute {
    pub span: Span,
    pub kind: AttributeKind,
}

#[derive(Debug, Clone)]
pub enum AttributeKind {
    Lang(EarlyAttrLang),
    Late(Obj<Expr>),
}

#[derive(Debug, Copy, Clone)]
pub struct EarlyAttrLang {
    pub name: Symbol,
}

// === Language Items === //

pub trait LangItemValidator: Sized {
    type Stored: fmt::Debug + Clone;

    fn as_item(&self, tcx: &TyCtxt, stored: Self::Stored) -> Obj<Item>;

    fn assign(
        &self,
        tcx: &TyCtxt,
        item: Obj<Item>,
        name: Symbol,
        span: Span,
    ) -> Result<Self::Stored, ErrorGuaranteed>;
}

#[derive(Debug, Copy, Clone, Default)]
pub struct TraitValidator;

impl LangItemValidator for TraitValidator {
    type Stored = Obj<TraitItem>;

    fn as_item(&self, tcx: &TyCtxt, stored: Self::Stored) -> Obj<Item> {
        stored.r(&tcx.session).item
    }

    fn assign(
        &self,
        tcx: &TyCtxt,
        item: Obj<Item>,
        name: Symbol,
        span: Span,
    ) -> Result<Self::Stored, ErrorGuaranteed> {
        item.r(&tcx.session).kind.as_trait().ok_or_else(|| {
            Diag::span_err(span, format_args!("`{name}` language item must be a trait")).emit()
        })
    }
}

macro_rules! define_lang_items {
    ($( $name:ident => $validator:ty $(, $validator_instance:expr)? ;)*) => {
        #[derive(Debug, Clone)]
        pub struct LangItems {
            $( $name: LateInit<<$validator as LangItemValidator>::Stored>, )*
        }

        impl Default for LangItems {
            fn default() -> Self {
                Self { $($name: LateInit::uninit()),* }
            }
        }

        impl LangItems {
            pub fn define(
                &self,
                tcx: &TyCtxt,
                name: Symbol,
                name_span: Span,
                item: Obj<Item>,
            ) -> Result<(), ErrorGuaranteed> {
                $({
                    thread_local! {
                        static VALIDATOR: $validator = define_lang_items!(
                            @pick_first $({ $validator_instance })? { Default::default() }
                        );
                    }

                    if name == symbol!(stringify!($name)) {
                        if let Some(&old) = LateInit::get(&self.$name) {
                            let old = VALIDATOR.with(|validator| validator.as_item(tcx, old));

                            let mut diag = Diag::span_err(
                                name_span,
                                format_args!(
                                    "language item `{name}` already defined at `{}`",
                                    old.r(&tcx.session).display_path(&tcx.session),
                                ),
                            );

                            if let Some(prev_name) = old.r(&tcx.session).name {
                                diag.push_child(
                                    LeafDiag::span_note(
                                        prev_name.span,
                                        "previously defined here",
                                    )
                                );
                            }

                            return Err(diag.emit());
                        }

                        let output = VALIDATOR.with(|validator| validator.assign(
                            tcx,
                            item,
                            name,
                            name_span
                        ))?;

                        LateInit::init(&self.$name, output);

                        return Ok(());
                    }
                })*

                Err(
                    Diag::span_err(
                        name_span,
                        format_args!("no such language item with name `{name}`"),
                    )
                    .emit(),
                )
            }

            $(
                pub fn $name(&self) -> Option<<$validator as LangItemValidator>::Stored> {
                    LateInit::get(&self.$name).cloned()
                }
            )*
        }
    };
    (@pick_first { $($first:tt)* } $({ $($remainder:tt)* })*) => {
        $($first)*
    }
}

define_lang_items! {
    deref_mut_trait => TraitValidator;
    deref_trait => TraitValidator;
    fn_mut_trait => TraitValidator;
    fn_once_trait => TraitValidator;
    fn_trait => TraitValidator;
    index_trait => TraitValidator;
}
