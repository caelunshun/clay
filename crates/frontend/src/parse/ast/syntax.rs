use crate::{
    base::{
        ErrorGuaranteed,
        syntax::{HasSpan, Span},
    },
    kw,
    parse::token::{Ident, Lifetime, TokenCharLit, TokenNumLit, TokenStrLit, TokenStream},
};
use std::rc::Rc;

// === Item === //

#[derive(Debug, Clone)]
pub enum AstItem {
    Mod(AstItemModule),
    Use(AstItemUse),
    Trait(AstItemTrait),
    Impl(AstItemImpl),
    Func(AstFnItem),
    Error(AstItemBase, ErrorGuaranteed),
}

impl AstItem {
    pub fn base(&self) -> &AstItemBase {
        let (AstItem::Mod(AstItemModule { base, .. })
        | AstItem::Use(AstItemUse { base, .. })
        | AstItem::Trait(AstItemTrait { base, .. })
        | AstItem::Impl(AstItemImpl { base, .. })
        | AstItem::Error(base, ..)
        | AstItem::Func(AstFnItem { base, .. })) = self;

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
    pub path: AstUsePath,
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
pub struct AstFnItem {
    pub base: AstItemBase,
    pub def: AstFnDef,
}

// === Item Helpers === //

#[derive(Debug, Clone)]
pub struct AstVisibility {
    pub span: Span,
    pub kind: AstVisibilityKind,
}

#[derive(Debug, Clone)]
pub enum AstVisibilityKind {
    Implicit,
    Priv,
    Pub,
    PubIn(AstSimplePath),
}

#[derive(Debug, Clone)]
pub struct AstAttribute {
    pub span: Span,
    pub is_inner: bool,
    pub path: AstSimplePath,
    pub args: TokenStream,
}

#[derive(Debug, Clone)]
pub struct AstSimplePath {
    pub span: Span,
    pub parts: Rc<[Ident]>,
}

impl AstSimplePath {
    pub fn as_ident(&self) -> Option<Ident> {
        self.parts.first().copied().filter(|v| {
            self.parts.len() == 1
                && !v.matches_kw(kw!("crate"))
                && !v.matches_kw(kw!("super"))
                && !v.matches_kw(kw!("self"))
        })
    }
}

#[derive(Debug, Clone)]
pub struct AstUsePath {
    pub span: Span,
    pub base: Rc<[Ident]>,
    pub kind: AstUsePathKind,
}

#[derive(Debug, Clone)]
pub enum AstUsePathKind {
    Direct(Option<Ident>),
    Wild(Span),
    Tree(Vec<AstUsePath>),
}

// === Clauses === //

#[derive(Debug, Clone)]
pub struct AstNamedSpec {
    pub span: Span,
    pub path: AstSimplePath,
    pub params: Option<AstGenericParamList>,
}

#[derive(Debug, Clone)]
pub struct AstTraitClauseList {
    pub span: Span,
    pub clauses: Vec<Result<AstTraitClause, ErrorGuaranteed>>,
}

#[derive(Debug, Clone)]
pub enum AstTraitClause {
    Outlives(Lifetime),
    Trait(AstNamedSpec),
}

#[derive(Debug, Clone)]
pub struct AstGenericParamList {
    pub span: Span,
    pub list: Vec<AstGenericParam>,
}

#[derive(Debug, Clone)]
pub struct AstGenericParam {
    pub span: Span,
    pub kind: AstGenericParamKind,
}

#[derive(Debug, Clone)]
pub enum AstGenericParamKind {
    /// A bare type (e.g. `u32`, `(u32, &'a i32)?`).
    PositionalTy(AstTy),

    /// A bare region (e.g. `'a`, `'_`)
    PositionalRe(Lifetime),

    /// A name with a clause list (e.g. `MyAssoc: Foo + Bar`, `T: 'gc`).
    InheritTy(Ident, AstTraitClauseList),

    /// A region with a clause list (e.g. `'a: 'b + 'c`).
    InheritRe(Lifetime, AstTraitClauseList),

    /// A name with an equality to a type (e.g. `MyAssoc = u32`).
    TyEquals(Ident, AstTy),
}

#[derive(Debug, Clone)]
pub enum AstGenericDef<'a> {
    Ty(Ident, Option<&'a AstTraitClauseList>),
    Re(Lifetime, Option<&'a AstTraitClauseList>),
}

impl AstGenericParamKind {
    pub fn as_generic_def(&self) -> Option<AstGenericDef<'_>> {
        match self {
            AstGenericParamKind::PositionalTy(ty) => {
                ty.as_ident().map(|ident| AstGenericDef::Ty(ident, None))
            }
            AstGenericParamKind::PositionalRe(re) => Some(AstGenericDef::Re(*re, None)),
            AstGenericParamKind::InheritTy(ident, clauses) => {
                Some(AstGenericDef::Ty(*ident, Some(clauses)))
            }
            AstGenericParamKind::InheritRe(re, clauses) => {
                Some(AstGenericDef::Re(*re, Some(clauses)))
            }
            AstGenericParamKind::TyEquals(..) => None,
        }
    }
}

// === Types === //

#[derive(Debug, Clone)]
pub enum AstTyOrRe {
    Re(Lifetime),
    Ty(AstTy),
}

impl HasSpan for AstTyOrRe {
    fn span(&self) -> Span {
        match self {
            AstTyOrRe::Re(v) => v.span,
            AstTyOrRe::Ty(v) => v.span,
        }
    }
}

#[derive(Debug, Clone)]
pub struct AstTy {
    pub span: Span,
    pub kind: AstTyKind,
}

#[derive(Debug, Clone)]
pub enum AstTyKind {
    This,
    Name(AstSimplePath, Option<AstGenericParamList>),
    Reference(Option<Lifetime>, Box<AstTy>),
    Trait(AstTraitClauseList),
    Tuple(Vec<AstTy>),
    Option(Box<AstTy>),
    Infer,
    Error(ErrorGuaranteed),
}

impl AstTy {
    pub fn as_ident(&self) -> Option<Ident> {
        match &self.kind {
            AstTyKind::Name(path, list) if list.is_none() => path.as_ident(),
            _ => None,
        }
    }
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
    Error(ErrorGuaranteed),
}

// === Functions === //

#[derive(Debug, Clone)]
pub struct AstFnDef {
    pub span: Span,
    pub name: Ident,
    pub generics: Option<AstGenericParamList>,
    pub args: Vec<AstFnArg>,
    pub ret_ty: Option<Box<AstTy>>,
    pub body: Option<AstBlock>,
}

#[derive(Debug, Clone)]
pub struct AstFnArg {
    pub span: Span,
    pub pat: Box<AstPat>,
    pub ty: Box<AstTy>,
}

#[derive(Debug, Clone)]
pub struct AstBlock {
    pub span: Span,
    pub stmts: Vec<AstStmt>,
    pub last_expr: Option<AstExpr>,
}

#[derive(Debug, Clone)]
pub struct AstStmt {
    pub span: Span,
    pub kind: AstStmtKind,
}

#[derive(Debug, Clone)]
pub enum AstStmtKind {
    Expr(AstExpr),
    Item(Box<AstItem>),
}

#[derive(Debug, Clone)]
pub struct AstExpr {
    pub span: Span,
    pub kind: AstExprKind,
}

// Adapted from: https://github.com/rust-lang/rust/blob/2286e5d224b3413484cf4f398a9f078487e7b49d/compiler/rustc_ast/src/ast.rs#L1731
#[derive(Debug, Clone)]
pub enum AstExprKind {
    Array(Vec<AstExpr>),
    Call(Box<AstExpr>, Vec<AstExpr>),
    Method(),
    Tuple(Vec<AstExpr>),
    Binary(AstBinOpKind, Box<AstExpr>, Box<AstExpr>),
    Unary(AstUnOpKind, Box<AstExpr>),
    Lit(AstFnExprLit),
    Cast(Box<AstExpr>, Box<AstTy>),
    Let(Box<AstPat>, Box<AstExpr>, Span),
    If(Box<AstExpr>, Box<AstBlock>, Option<Box<AstExpr>>),
    While(Box<AstExpr>, Box<AstBlock>, Option<Lifetime>),
    ForLoop {
        pat: Box<AstPat>,
        iter: Box<AstExpr>,
        body: Box<AstBlock>,
        label: Option<Lifetime>,
    },
    Loop(Box<AstBlock>, Option<Lifetime>),
    Match(Box<AstExpr>, Vec<AstMatchArm>),
    // Closure(Box<AstClosure>),
    Block(Box<AstBlock>, Option<Lifetime>),
    Assign(Box<AstExpr>, Box<AstExpr>),
    AssignOp(AstBinOpKind, Box<AstExpr>, Box<AstExpr>),
    Field(Box<AstExpr>, Ident),
    Index(Box<AstExpr>, Box<AstExpr>),
    Range(Option<Box<AstExpr>>, Option<Box<AstExpr>>, AstRangeLimits),
    Underscore,
    Path(AstExprPath),
    AddrOf(AstMutability, Box<AstExpr>),
    Break(Option<Lifetime>, Option<Box<AstExpr>>),
    Continue(Option<Lifetime>),
    Return(Option<Box<AstExpr>>),
    Struct(AstExprPath, Vec<AstExprField>, AstStructRest),
}

#[derive(Debug, Clone)]
pub enum AstFnExprLit {
    Number(TokenNumLit),
    Char(TokenCharLit),
    String(TokenStrLit),
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum AstBinOpKind {
    /// The `+` operator (addition)
    Add,
    /// The `-` operator (subtraction)
    Sub,
    /// The `*` operator (multiplication)
    Mul,
    /// The `/` operator (division)
    Div,
    /// The `%` operator (modulus)
    Rem,
    /// The `&&` operator (logical and)
    And,
    /// The `||` operator (logical or)
    Or,
    /// The `^` operator (bitwise xor)
    BitXor,
    /// The `&` operator (bitwise and)
    BitAnd,
    /// The `|` operator (bitwise or)
    BitOr,
    /// The `<<` operator (shift left)
    Shl,
    /// The `>>` operator (shift right)
    Shr,
    /// The `==` operator (equality)
    Eq,
    /// The `<` operator (less than)
    Lt,
    /// The `<=` operator (less than or equal to)
    Le,
    /// The `!=` operator (not equal to)
    Ne,
    /// The `>=` operator (greater than or equal to)
    Ge,
    /// The `>` operator (greater than)
    Gt,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum AstUnOpKind {
    /// The `*` operator for dereferencing
    Deref,
    /// The `!` operator for logical inversion
    Not,
    /// The `-` operator for negation
    Neg,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum AstRangeLimits {
    /// Inclusive at the beginning, exclusive at the end.
    HalfOpen,
    /// Inclusive at the beginning and end.
    Closed,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum AstMutability {
    Mut(Span),
    Ref(Span),
    Implicit,
}

#[derive(Debug, Clone)]
pub struct AstExprField {
    pub ident: Ident,
    pub expr: Box<AstExpr>,
    pub is_shorthand: bool,
}

#[derive(Debug, Clone)]
pub enum AstStructRest {
    /// `..x`.
    Base(Box<AstExpr>),
    /// `..`.
    Rest(Span),
    /// No trailing `..` or expression.
    None,
}

// === Paths === //

#[derive(Debug, Clone)]
pub struct AstExprPath {
    pub span: Span,
    pub segments: Rc<[AstExprPathSegment]>,
}

#[derive(Debug, Clone)]
pub struct AstExprPathSegment {
    pub part: Ident,
    pub args: Option<Box<AstGenericParamList>>,
}

#[derive(Debug, Clone)]
pub struct AstExprQualification {
    pub span: Span,
    pub src_ty: AstTy,
    pub as_trait: Option<AstTy>,
}

// === Patterns === //

#[derive(Debug, Clone)]
pub struct AstPat {
    pub span: Span,
    pub kind: AstPatKind,
}

#[derive(Debug, Clone)]
pub enum AstPatKind {
    Wild,
    Ident(AstBindingMode, Ident, Option<Box<AstPat>>),
    Struct(AstExprPath, Vec<AstPatField>, AstPatStructRest),
    TupleStruct(AstExprPath, Vec<AstPat>),
    Or(Vec<AstPat>),
    Tuple(Vec<AstPat>),
    Error(ErrorGuaranteed),
    // TODO
}

#[derive(Debug, Copy, Clone)]
pub struct AstBindingMode {
    pub by_ref: Option<AstMutability>,
    pub local_muta: AstMutability,
}

#[derive(Debug, Clone)]
pub struct AstPatField {
    pub span: Span,
    pub name: Ident,
    pub pat: Box<AstPat>,
    pub is_shorthand: bool,
}

#[derive(Debug, Copy, Clone)]
pub enum AstPatStructRest {
    Rest(Span),
    Recovered(ErrorGuaranteed),
    None,
}

#[derive(Debug, Clone)]
pub struct AstMatchArm {
    pub span: Span,
    pub pat: Box<AstPat>,
    pub guard: Option<Box<AstExpr>>,
    pub body: Option<Box<AstExpr>>,
}
