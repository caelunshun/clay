use crate::{
    base::{
        Session,
        arena::{LateInit, Obj},
        syntax::{Span, Symbol},
    },
    semantic::syntax::{Crate, Expr, Item, TraitItem},
    symbol,
};

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

#[derive(Debug, Clone)]
pub enum LangItemDefineError {
    NoSuchName,
    AlreadyDefined(Obj<Item>),
}

macro_rules! define_lang_items {
    ($( $name:ident ),*$(,)?) => {
        #[derive(Debug, Clone)]
        pub struct LangItems {
            $( $name: LateInit<Obj<Item>>, )*
        }

        impl Default for LangItems {
            fn default() -> Self {
                Self { $($name: LateInit::uninit()),* }
            }
        }

        impl LangItems {
            pub fn define(
                &self,
                name: Symbol,
                item: Obj<Item>,
            ) -> Result<(), LangItemDefineError> {
                $(
                    if name == symbol!(stringify!($name)) {
                        if let Some(&old) = LateInit::get(&self.$name) {
                            return Err(LangItemDefineError::AlreadyDefined(old));
                        }

                        LateInit::init(&self.$name, item);
                        return Ok(());
                    }
                )*

                Err(LangItemDefineError::NoSuchName)
            }

            $(
                pub fn $name(&self) -> Option<Obj<Item>> {
                    LateInit::get(&self.$name).copied()
                }
            )*
        }
    };
}

define_lang_items! {
    deref_mut_trait,
    deref_trait,
    fn_mut_trait,
    fn_once_trait,
    fn_trait,
}

impl Crate {
    pub fn deref_lang_item(&self, s: &Session) -> Option<Obj<TraitItem>> {
        self.lang_items
            .deref_trait()
            .map(|v| v.r(s).kind.as_trait().unwrap())
    }

    pub fn fn_once_lang_item(&self, s: &Session) -> Option<Obj<TraitItem>> {
        self.lang_items
            .fn_once_trait()
            .map(|v| v.r(s).kind.as_trait().unwrap())
    }
}
