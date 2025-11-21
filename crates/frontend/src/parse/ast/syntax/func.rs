use crate::{
    base::{ErrorGuaranteed, syntax::Span},
    parse::{
        ast::{AstExprPath, AstGenericParamList, AstItem, AstOptMutability, AstReturnTy, AstTy},
        token::{Ident, Lifetime, TokenCharLit, TokenNumLit, TokenStrLit},
    },
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
    Let(Box<AstPat>, Option<Box<AstExpr>>),
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
    Paren(Box<AstExpr>),
    Tuple(Vec<AstExpr>),
    Binary(AstBinOpKind, Box<AstExpr>, Box<AstExpr>),
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
    AssignOp(AstBinOpKind, Box<AstExpr>, Box<AstExpr>),
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
            | AstExprKind::Method(..)
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

#[derive(Debug, Clone)]
pub enum AstLit {
    Number(TokenNumLit),
    Char(TokenCharLit),
    String(TokenStrLit),
    Bool(AstBoolLit),
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct AstBoolLit {
    pub span: Span,
    pub value: bool,
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

// === Patterns === //

#[derive(Debug, Clone)]
pub struct AstPat {
    pub span: Span,
    pub kind: AstPatKind,
}

#[derive(Debug, Clone)]
pub enum AstPatKind {
    Wild,
    Path {
        binding_mode: AstBindingMode,
        path: AstExprPath,
        and_bind: Option<Box<AstPat>>,
    },
    PathAndBrace(AstExprPath, Vec<AstPatField>, AstPatStructRest),
    PathAndParen(AstExprPath, Vec<AstPat>),
    Or(Vec<AstPat>),
    Tuple(Vec<AstPat>),
    Error(ErrorGuaranteed),
    // TODO
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
    pub body: Box<AstExpr>,
}
