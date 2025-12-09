use crate::{
    base::{
        ErrorGuaranteed,
        syntax::{HasSpan, Span},
    },
    parse::{
        ast::{
            AnyPunct, AstGenericParamList, AstItem, AstOptMutability, AstParamedPath, AstReturnTy,
            AstTy,
        },
        token::{Ident, Lifetime, TokenCharLit, TokenNumLit, TokenStrLit},
    },
    punct, puncts,
};

// === Functions === //

#[derive(Debug, Clone)]
pub struct AstFnDef {
    pub span: Span,
    pub name: Ident,
    pub generics: Option<AstGenericParamList>,
    pub args: Vec<AstFnArg>,
    pub ret_ty: AstReturnTy,
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
    Let(AstStmtLet),
    Item(Box<AstItem>),
}

#[derive(Debug, Clone)]
pub struct AstStmtLet {
    pub pat: Box<AstPat>,
    pub ascription: Option<Box<AstTy>>,
    pub init: Option<Box<AstExpr>>,
    pub else_clause: Option<Box<AstBlock>>,
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
    GenericMethodCall {
        target: Box<AstExpr>,
        method: Ident,
        generics: Box<AstGenericParamList>,
        args: Vec<AstExpr>,
    },
    Paren(Box<AstExpr>),
    Tuple(Vec<AstExpr>),
    Binary(AstBinOpSpanned, Box<AstExpr>, Box<AstExpr>),
    Unary(AstUnOpKind, Box<AstExpr>),
    Lit(AstLit),
    Cast(Box<AstExpr>, Box<AstTy>),
    Let(Box<AstPat>, Box<AstExpr>, Span),
    If {
        cond: Box<AstExpr>,
        truthy: Box<AstBlock>,
        falsy: Option<Box<AstExpr>>,
    },
    While {
        cond: Box<AstExpr>,
        block: Box<AstBlock>,
        label: Option<Lifetime>,
    },
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
    AssignOp(AstAssignOpKind, Box<AstExpr>, Box<AstExpr>),
    Field(Box<AstExpr>, Ident),
    Index(Box<AstExpr>, Box<AstExpr>),
    Range(Option<Box<AstExpr>>, Option<Box<AstExpr>>, AstRangeLimits),
    Underscore,
    Path(AstExprPath),
    AddrOf(AstOptMutability, Box<AstExpr>),
    Break(Option<Lifetime>, Option<Box<AstExpr>>),
    Continue(Option<Lifetime>),
    Return(Option<Box<AstExpr>>),
    Struct(AstExprPath, Vec<AstExprField>, AstStructRest),
    Error(ErrorGuaranteed),
}

impl AstExprKind {
    pub fn needs_semi(&self) -> bool {
        match self {
            AstExprKind::Array(..)
            | AstExprKind::Call(..)
            | AstExprKind::Paren(..)
            | AstExprKind::Tuple(..)
            | AstExprKind::Binary(..)
            | AstExprKind::Unary(..)
            | AstExprKind::Lit(..)
            | AstExprKind::Cast(..)
            | AstExprKind::Let(..)
            | AstExprKind::Assign(..)
            | AstExprKind::AssignOp(..)
            | AstExprKind::Field(..)
            | AstExprKind::GenericMethodCall { .. }
            | AstExprKind::Index(..)
            | AstExprKind::Range(..)
            | AstExprKind::Underscore
            | AstExprKind::Path(..)
            | AstExprKind::AddrOf(..)
            | AstExprKind::Break(..)
            | AstExprKind::Continue(..)
            | AstExprKind::Return(..)
            | AstExprKind::Struct(..) => true,

            AstExprKind::If { .. }
            | AstExprKind::While { .. }
            | AstExprKind::ForLoop { .. }
            | AstExprKind::Loop(..)
            | AstExprKind::Match(..)
            | AstExprKind::Block(..)
            | AstExprKind::Error(..) => false,
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum AstLit {
    Number(TokenNumLit),
    Char(TokenCharLit),
    String(TokenStrLit),
    Bool(AstBoolLit),
}

impl HasSpan for AstLit {
    fn span(&self) -> Span {
        match self {
            AstLit::Number(v) => v.span,
            AstLit::Char(v) => v.span,
            AstLit::String(v) => v.span,
            AstLit::Bool(v) => v.span,
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct AstBoolLit {
    pub span: Span,
    pub value: bool,
}

#[derive(Debug, Copy, Clone)]
pub struct AstBinOpSpanned {
    pub span: Span,
    pub kind: AstBinOpKind,
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

impl AstBinOpKind {
    pub fn punct(self) -> AnyPunct {
        match self {
            AstBinOpKind::Add => punct!('+').into(),
            AstBinOpKind::Sub => punct!('-').into(),
            AstBinOpKind::Mul => punct!('*').into(),
            AstBinOpKind::Div => punct!('/').into(),
            AstBinOpKind::Rem => punct!('%').into(),
            AstBinOpKind::And => puncts!("&&").into(),
            AstBinOpKind::Or => puncts!("||").into(),
            AstBinOpKind::BitXor => punct!('^').into(),
            AstBinOpKind::BitAnd => punct!('&').into(),
            AstBinOpKind::BitOr => punct!('|').into(),
            AstBinOpKind::Shl => puncts!("<<").into(),
            AstBinOpKind::Shr => puncts!(">>").into(),
            AstBinOpKind::Eq => puncts!("==").into(),
            AstBinOpKind::Lt => punct!('<').into(),
            AstBinOpKind::Le => puncts!("<=").into(),
            AstBinOpKind::Ne => puncts!("!=").into(),
            AstBinOpKind::Ge => punct!('>').into(),
            AstBinOpKind::Gt => puncts!(">=").into(),
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum AstAssignOpKind {
    /// The `+=` operator (addition)
    Add,
    /// The `-=` operator (subtraction)
    Sub,
    /// The `*=` operator (multiplication)
    Mul,
    /// The `/=` operator (division)
    Div,
    /// The `%=` operator (modulus)
    Rem,
    /// The `^=` operator (bitwise xor)
    BitXor,
    /// The `&=` operator (bitwise and)
    BitAnd,
    /// The `|=` operator (bitwise or)
    BitOr,
    /// The `<<=` operator (shift left)
    Shl,
    /// The `>>=` operator (shift right)
    Shr,
}

impl AstAssignOpKind {
    pub fn punct(self) -> AnyPunct {
        match self {
            AstAssignOpKind::Add => puncts!("+=").into(),
            AstAssignOpKind::Sub => puncts!("-=").into(),
            AstAssignOpKind::Mul => puncts!("*=").into(),
            AstAssignOpKind::Div => puncts!("/=").into(),
            AstAssignOpKind::Rem => puncts!("%=").into(),
            AstAssignOpKind::BitXor => puncts!("^=").into(),
            AstAssignOpKind::BitAnd => puncts!("&=").into(),
            AstAssignOpKind::BitOr => puncts!("|=").into(),
            AstAssignOpKind::Shl => puncts!("<<=").into(),
            AstAssignOpKind::Shr => puncts!(">>=").into(),
        }
    }
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

#[derive(Debug, Clone)]
pub struct AstExprField {
    pub name: Ident,
    pub expr: Option<Box<AstExpr>>,
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

#[derive(Debug, Clone)]
pub struct AstExprPath {
    pub span: Span,
    pub kind: AstExprPathKind,
}

#[derive(Debug, Clone)]
pub enum AstExprPathKind {
    /// A bare path with some generic parameterizations.
    Bare(AstParamedPath),

    /// A path starting with `Self` with an optional rest.
    SelfTy(Span, Option<AstParamedPath>),

    /// A path starting with an explicit qualifier with an mandatory rest path.
    Qualified(Box<AstQualification>, AstParamedPath),

    /// An invalid path.
    Error(ErrorGuaranteed),
}

#[derive(Debug, Clone)]
pub struct AstQualification {
    pub span: Span,
    pub self_ty: AstTy,
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
    Hole,
    Path {
        binding_mode: AstBindingMode,
        path: AstExprPath,
        and_bind: Option<Box<AstPat>>,
    },
    PathAndBrace(AstExprPath, Vec<AstPatField>, AstPatStructRest),
    PathAndParen(AstExprPath, Vec<AstPat>),
    Or(Vec<AstPat>),
    Tuple(Vec<AstPat>),
    Ref(AstOptMutability, Box<AstPat>),
    Slice(Vec<AstPat>),
    Rest,
    Paren(Box<AstPat>),
    Range(Option<Box<AstExpr>>, Option<Box<AstExpr>>, AstRangeLimits),
    Lit(Box<AstExpr>),
    Error(ErrorGuaranteed),
}

#[derive(Debug, Copy, Clone)]
pub struct AstBindingMode {
    pub by_ref: AstOptMutability,
    pub local_muta: AstOptMutability,
}

impl AstBindingMode {
    pub fn was_specified(self) -> bool {
        self.by_ref.was_explicit() || self.local_muta.was_explicit()
    }
}

impl HasSpan for AstBindingMode {
    fn span(&self) -> Span {
        match (self.by_ref.as_explicit(), self.local_muta.as_explicit()) {
            (Some(v), None) | (None, Some(v)) => v.span(),
            (Some(lhs), Some(rhs)) => lhs.span().to(rhs.span()),
            (None, None) => Span::DUMMY,
        }
    }
}

#[derive(Debug, Clone)]
pub struct AstPatField {
    pub span: Span,
    pub name: Ident,
    pub kind: AstPatFieldKind,
}

#[derive(Debug, Clone)]
pub enum AstPatFieldKind {
    Bare(AstOptMutability),
    WithPat(Box<AstPat>),
}

#[derive(Debug, Copy, Clone)]
pub enum AstPatStructRest {
    Rest(Span),
    None,
}

#[derive(Debug, Clone)]
pub struct AstMatchArm {
    pub span: Span,
    pub pat: Box<AstPat>,
    pub guard: Option<Box<AstExpr>>,
    pub body: Box<AstExpr>,
}
