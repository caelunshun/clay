use crate::{
    base::{ErrorGuaranteed, syntax::Span},
    parse::{
        ast::{
            AstAttribute, AstFnDef, AstGenericParamList, AstTraitClauseList, AstTreePath, AstTy,
            AstVisibility,
        },
        token::Ident,
    },
};

// === Item === //

#[derive(Debug, Clone)]
pub enum AstItem {
    Mod(AstItemModule),
    Use(AstItemUse),
    Trait(AstItemTrait),
    Impl(AstItemImpl),
    Func(AstItemFn),
    Struct(AstItemStruct),
    Enum(AstItemEnum),
    Error(AstItemBase, ErrorGuaranteed),
}

impl AstItem {
    pub fn base(&self) -> &AstItemBase {
        let (AstItem::Mod(AstItemModule { base, .. })
        | AstItem::Use(AstItemUse { base, .. })
        | AstItem::Trait(AstItemTrait { base, .. })
        | AstItem::Impl(AstItemImpl { base, .. })
        | AstItem::Func(AstItemFn { base, .. })
        | AstItem::Struct(AstItemStruct { base, .. })
        | AstItem::Enum(AstItemEnum { base, .. })
        | AstItem::Error(base, ..)) = self;

        base
    }
}

#[derive(Debug, Clone)]
pub struct AstItemBase {
    pub span: Span,
    pub outer_attrs: Vec<AstAttribute>,
    pub vis: AstVisibility,
}

#[derive(Debug, Clone)]
pub struct AstItemModule {
    pub base: AstItemBase,
    pub name: Ident,
    pub contents: Option<AstItemModuleContents>,
}

#[derive(Debug, Clone)]
pub struct AstItemModuleContents {
    pub inner_attrs: Vec<AstAttribute>,
    pub items: Vec<AstItem>,
}

#[derive(Debug, Clone)]
pub struct AstItemUse {
    pub base: AstItemBase,
    pub path: AstTreePath,
}

#[derive(Debug, Clone)]
pub struct AstItemTrait {
    pub base: AstItemBase,
    pub name: Ident,
    pub generics: Option<AstGenericParamList>,
    pub inherits: Option<AstTraitClauseList>,
    pub body: AstImplLikeBody,
}

#[derive(Debug, Clone)]
pub struct AstItemImpl {
    pub base: AstItemBase,
    pub generics: Option<AstGenericParamList>,
    pub first_ty: AstTy,
    pub second_ty: Option<AstTy>,
    pub body: AstImplLikeBody,
}

#[derive(Debug, Clone)]
pub struct AstItemFn {
    pub base: AstItemBase,
    pub def: AstFnDef,
}

#[derive(Debug, Clone)]
pub struct AstItemStruct {
    pub base: AstItemBase,
    pub name: Ident,
    pub generics: Option<AstGenericParamList>,
    pub kind: AstStructKind,
}

#[derive(Debug, Clone)]
pub enum AstStructKind {
    Unit,
    Tuple(Vec<AstStructAnonField>),
    Struct(Vec<AstStructNamedField>),
}

impl AstStructKind {
    pub fn needs_semi(&self) -> bool {
        match self {
            AstStructKind::Unit => true,
            AstStructKind::Tuple(..) => true,
            AstStructKind::Struct(..) => false,
        }
    }
}

#[derive(Debug, Clone)]
pub struct AstStructAnonField {
    pub span: Span,
    pub vis: AstVisibility,
    pub ty: AstTy,
}

#[derive(Debug, Clone)]
pub struct AstStructNamedField {
    pub span: Span,
    pub vis: AstVisibility,
    pub name: Ident,
    pub ty: AstTy,
}

#[derive(Debug, Clone)]
pub struct AstItemEnum {
    pub base: AstItemBase,
    pub name: Ident,
    pub generics: Option<AstGenericParamList>,
    pub variants: Vec<AstEnumVariant>,
}

#[derive(Debug, Clone)]
pub struct AstEnumVariant {
    pub span: Span,
    pub name: Ident,
    pub kind: AstStructKind,
}

// === Impl-like Bodies === //

#[derive(Debug, Clone)]
pub struct AstImplLikeBody {
    pub span: Span,
    pub members: Vec<AstImplLikeMember>,
}

#[derive(Debug, Clone)]
pub struct AstImplLikeMember {
    pub span: Span,
    pub vis: AstVisibility,
    pub kind: AstImplLikeMemberKind,
}

#[derive(Debug, Clone)]
pub enum AstImplLikeMemberKind {
    TypeEquals(Ident, AstTy),
    TypeInherits(Ident, AstTraitClauseList),
    Func(AstFnDef),
    Error(ErrorGuaranteed),
}
