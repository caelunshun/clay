use crate::{
    base::{
        ErrorGuaranteed,
        syntax::{Span, Symbol},
    },
    parse::token::{Ident, TokenCharLit, TokenNumLit, TokenStrLit},
    symbol,
};

// === ASTs === //

#[derive(Debug, Clone)]
pub struct AstAdt {
    pub span: Span,
    pub kind: AdtKind,
    pub fields: Vec<AstField>,
    pub members: Vec<AstMember>,
}

#[derive(Debug, Clone)]
pub struct AstField {
    pub name: Ident,
    pub ty: Box<AstExpr>,
    pub is_public: bool,
}

#[derive(Debug, Clone)]
pub struct AstMember {
    pub name: Ident,
    pub init: Box<AstExpr>,
    pub is_public: bool,
}

// === Expressions === //

#[derive(Debug, Clone)]
pub struct AstExpr {
    pub span: Span,
    pub kind: AstExprKind,
}

#[derive(Debug, Clone)]
#[rustfmt::skip]
pub enum AstExprKind {
    // === Seeds === //

    /// A name expression (e.g. a local, a generic, an upvar, ...).
    ///
    /// Can be parsed in both type and expression parsing contexts.
    Name(Ident),

    /// A literal expression.
    ///
    /// Can be parsed in both type and expression parsing contexts.
    Lit(LiteralKind),

    /// A parenthesized expression (e.g. `(foo)`).
    ///
    /// Can be parsed in both type and expression parsing contexts. The sub-expressions inherit the
    /// parsing context of their parent.
    Paren(Box<AstExpr>),

    /// A block expression (e.g. `{ let x = 2; x }`).
    ///
    /// Can be parsed in both type and expression parsing contexts. Always parses its contents in
    /// an expression context.
    Block(Box<AstBlock>),

    /// A constant block expression (e.g. `const { let x = 2; x }`).
    ///
    /// Can be parsed in both type and expression parsing contexts. Always parses its contents in
    /// an expression context.
    ConstBlock(Box<AstBlock>),

    /// An ADT literal (e.g. `struct {}`, `mod {}`).
    ///
    /// Can be parsed in both type and expression parsing contexts.
    AdtDef(Box<AstAdt>),

    /// A no-op expression whose contents are parsed in a type context
    /// (e.g. `return type(*const u32)`).
    ///
    /// Can only be parsed in expression parsing contexts.
    TypeExpr(Box<AstExpr>),

    /// A tuple constructor (e.g. `(foo, bar)` or `(baz,)`).
    ///
    /// Can only be parsed in expression parsing contexts.
    Tuple(Vec<AstExpr>),

    /// An array constructor (e.g. `[foo, bar]` or `[baz]`).
    ///
    /// Can only be parsed in expression parsing contexts.
    Array(Vec<AstExpr>),

    /// A struct instance constructor (e.g. `my.Type { x, y }`).
    ///
    /// Can only be parsed in expression parsing contexts.
    New(Box<AstExpr>, Vec<(Ident, Option<Box<AstExpr>>)>),

    /// An `if` expression (e.g. `if foo { bar }`, `if cond { abc } else { def }`, or
    /// `if cond { hi } else if cond { hello }`).
    ///
    /// Can only be parsed in expression parsing contexts.
    If {
        cond: Box<AstExpr>,
        truthy: Box<AstBlock>,
        falsy: Option<Box<AstBlock>>,
    },

    /// An `while` expression (e.g. `while foo { bar }`).
    ///
    /// Can only be parsed in expression parsing contexts.
    While {
        cond: Box<AstExpr>,
        block: Box<AstBlock>,
    },

    /// A `loop` expression (e.g. `loop { baz }`).
    ///
    /// Can only be parsed in expression parsing contexts.
    Loop(Box<AstBlock>),

    /// A `match` expression (e.g. `match foo { (bar, baz) => ..., _ => ... }`).
    ///
    /// Can only be parsed in expression parsing contexts.
    Match {
        scrutinee: Box<AstExpr>,
        arms: Vec<AstMatchArm>,
    },

    /// A `return` expression (e.g. `return`, `return foo`).
    ///
    /// Can only be parsed in expression parsing contexts.
    Return(Option<Box<AstExpr>>),

    /// A `continue` expression (e.g. `continue`).
    ///
    /// Can only be parsed in expression parsing contexts.
    Continue,

    /// A `break` expression (e.g. `break`, `break foo`).
    ///
    /// Can only be parsed in expression parsing contexts.
    Break(Option<Box<AstExpr>>),

    /// A `fn` expression (e.g. `fn<T: type>(v: T) -> T { v }`).
    ///
    /// Can only be parsed in expression parsing contexts.
    FuncDef(Box<AstFuncDef>),

    /// An intrinsic fetch expression (e.g. `intrinsic("my_intrinsic")`).
    ///
    /// Can be parsed in both type and expression parsing contexts.
    Intrinsic(Symbol),

    /// A use expression (e.g. `use("path/to/other.sdl")`).
    ///
    /// Can only be parsed in expression parsing contexts.
    Use(Box<TokenStrLit>),

    // === Prefix === //

    /// A unary operation (e.g. `-foo`).
    ///
    /// Can only be parsed in expression parsing contexts.
    Unary(UnaryOpKind, Box<AstExpr>),

    // === Infix === //

    /// A binary operator expression (e.g. `foo + bar`).
    ///
    /// Can only be parsed in expression parsing contexts.
    Bin(BinOpKind, Box<AstExpr>, Box<AstExpr>),

    /// An assignment expression (e.g. `foo = bar`).
    ///
    /// Can only be parsed in expression parsing contexts.
    Assign(Box<AstExpr>, Box<AstExpr>),

    // === Postfix === //

    /// Array indexing (e.g. `foo[3]`).
    ///
    /// Can only be parsed in expression parsing contexts. The sub-expressions inherit the parsing
    /// context of their parent.
    Index(Box<AstExpr>, Box<AstExpr>),

    /// A function call (e.g. `foo(a, b, c)`).
    ///
    /// Can be parsed in both type and expression parsing contexts. The sub-expressions inherit the
    /// parsing context of their parent.
    Call(Box<AstExpr>, Vec<AstExpr>),

    /// Function instantiation (e.g. `Array.<u32, {8}>` or `Array.<<u32, {8}>>`).
    ///
    /// Can be parsed in both type and expression parsing contexts. The instantiation arguments are
    /// always parsed as types.
    /// 
    /// Usually, this expression is placed in its own constant context to allow for static typing.
    /// The `<<...>>` syntax can be used to
    Instantiate {
        target: Box<AstExpr>,
        generics: Vec<AstExpr>,
        is_dynamic: bool,
    },

    /// A named indexing operation (e.g. `foo.bar`).
    ///
    /// Can be parsed in both type and expression parsing contexts.The sub-expressions inherit the
    /// parsing context of their parent.
    NamedIndex(Box<AstExpr>, Ident),

    // === Type Constructors === //

    /// A type constructor for tuples (e.g. `(Foo, Bar)`).
    ///
    /// Can only be parsed in type parsing contexts.
    TypeTuple(Vec<AstExpr>),

    /// A type constructor for arrays (e.g. `[Foo; 3]`).
    ///
    /// Can only be parsed in type parsing contexts. The element type is parsed as a type but the
    /// length is parsed as a normal expression.
    TypeArray(Box<AstExpr>, Box<AstExpr>),

    /// A type constructor for pointers (e.g. `*const u32`, `*mut i32`).
    ///
    /// Can only be parsed in type parsing contexts.
    TypePointer(Mutability, Box<AstExpr>),

    /// A type constructor for function pointers (e.g. `fn(Foo, Bar, Baz) -> Maz`).
    ///
    /// Can only be parsed in type parsing contexts.
    TypeFn(Vec<AstExpr>, Option<Box<AstExpr>>),

    /// A meta-type type constructor (e.g. `fn...`, `type`, `sym`).
    ///
    /// Can only be parsed in type parsing contexts.
    TypeMeta(MetaTypeKind),

    /// The `Self` type (e.g. `Self`).
    ///
    /// Can only be parsed in type parsing contexts.
    TypeSelf,

    // === Misc === //

    /// An invalid expression placeholder.
    Error(ErrorGuaranteed),
}

impl AstExprKind {
    pub fn needs_semi(&self) -> bool {
        match self {
            AstExprKind::Block(..)
            | AstExprKind::ConstBlock(..)
            | AstExprKind::If { .. }
            | AstExprKind::While { .. }
            | AstExprKind::Loop(..)
            | AstExprKind::Match { .. } => false,
            AstExprKind::Name(..)
            | AstExprKind::Lit(..)
            | AstExprKind::Paren(..)
            | AstExprKind::AdtDef(..)
            | AstExprKind::TypeExpr(..)
            | AstExprKind::New(..)
            | AstExprKind::Tuple(..)
            | AstExprKind::Array(..)
            | AstExprKind::Return(..)
            | AstExprKind::Continue
            | AstExprKind::Break(..)
            | AstExprKind::FuncDef(..)
            | AstExprKind::Intrinsic(..)
            | AstExprKind::Use(..)
            | AstExprKind::Unary(..)
            | AstExprKind::Bin(..)
            | AstExprKind::Assign(..)
            | AstExprKind::Index(..)
            | AstExprKind::Instantiate { .. }
            | AstExprKind::Call(..)
            | AstExprKind::NamedIndex(..)
            | AstExprKind::TypeTuple(..)
            | AstExprKind::TypeArray(..)
            | AstExprKind::TypePointer(..)
            | AstExprKind::TypeFn(..)
            | AstExprKind::TypeMeta(..)
            | AstExprKind::TypeSelf
            | AstExprKind::Error(..) => true,
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum BinOpKind {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
    BitAnd,
    BitOr,
    BitXor,
    LogicalAnd,
    LogicalOr,
    Eq,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum UnaryOpKind {
    Neg,
    Not,
}

#[derive(Debug, Copy, Clone)]
pub enum LiteralKind {
    /// A boolean literal (e.g. `true` or `false`).
    BoolLit(bool),

    /// A string literal (e.g. `"whee"`).
    StrLit(TokenStrLit),

    /// A character literal (e.g. `'a'`).
    CharLit(TokenCharLit),

    /// A numeric literal (e.g. `123`, `0xBADF00D`, or `4.34E-4`).
    NumLit(TokenNumLit),
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum AdtKind {
    Mod,
    Struct,
    Union,
    Enum,
}

impl AdtKind {
    pub fn can_have_fields(self) -> bool {
        !matches!(self, AdtKind::Mod)
    }

    pub fn what(self) -> Symbol {
        match self {
            AdtKind::Mod => symbol!("module"),
            AdtKind::Struct => symbol!("structure"),
            AdtKind::Union => symbol!("union"),
            AdtKind::Enum => symbol!("enum"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct AstMatchArm {
    pub pat: AstPat,
    pub expr: AstExpr,
}

#[derive(Debug, Clone)]
pub struct AstBlock {
    pub label: Option<Ident>,
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
    Let { binding: AstPat, init: Box<AstExpr> },
    Const { name: Ident, init: Box<AstExpr> },
}

#[derive(Debug, Clone)]
pub struct AstPat {
    pub span: Span,
    pub kind: AstPatKind,
}

#[derive(Debug, Clone)]
pub enum AstPatKind {
    Hole,
    Name(Mutability, Ident),
    Tuple(Vec<AstPat>),
    Paren(Box<AstPat>),
    Error(ErrorGuaranteed),
}

#[derive(Debug, Clone)]
pub struct AstFuncDef {
    pub sig_span: Span,
    pub generics: Vec<AstFuncGeneric>,
    pub params: Option<Vec<AstFuncParam>>,
    pub ret_ty: Option<Box<AstExpr>>,
    pub body: Box<AstBlock>,
}

#[derive(Debug, Clone)]
pub struct AstFuncGeneric {
    pub span: Span,
    pub name: Result<Ident, ErrorGuaranteed>,
    pub ty: AstExpr,
}

#[derive(Debug, Clone)]
pub struct AstFuncParam {
    pub span: Span,
    pub binding: AstPat,
    pub ty: AstExpr,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum MetaTypeKind {
    Fn,
    Sym,
    Type,
}

// === Mutability === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum Mutability {
    Not,
    Mut,
}

impl Mutability {
    pub fn is_not(self) -> bool {
        matches!(self, Mutability::Not)
    }

    pub fn is_mut(self) -> bool {
        matches!(self, Mutability::Mut)
    }
}

// === Binding Powers === //

pub mod expr_bp {
    use crate::base::syntax::{InfixBp, PostfixBp, PrefixBp};

    pub const PRE_NEG: PrefixBp = PrefixBp::new(9);
    pub const PRE_NOT: PrefixBp = PrefixBp::new(9);
    pub const PRE_RETURN: PrefixBp = PrefixBp::new(1);
    pub const PRE_BREAK: PrefixBp = PrefixBp::new(1);

    pub const INFIX_ADD: InfixBp = InfixBp::new_left(2);
    pub const INFIX_SUB: InfixBp = InfixBp::new_left(2);
    pub const INFIX_MUL: InfixBp = InfixBp::new_left(3);
    pub const INFIX_DIV: InfixBp = InfixBp::new_left(3);
    pub const INFIX_MOD: InfixBp = InfixBp::new_left(3);
    pub const INFIX_POW: InfixBp = InfixBp::new_left(3);
    pub const INFIX_EQ: InfixBp = InfixBp::new_left(3); // FIXME
    pub const INFIX_BIT_AND: InfixBp = InfixBp::new_left(3); // FIXME
    pub const INFIX_BIT_OR: InfixBp = InfixBp::new_left(3); // FIXME
    pub const INFIX_BIT_XOR: InfixBp = InfixBp::new_left(3); // FIXME
    pub const INFIX_LOGICAL_AND: InfixBp = InfixBp::new_left(3); // FIXME
    pub const INFIX_LOGICAL_OR: InfixBp = InfixBp::new_left(3); // FIXME
    pub const INFIX_ASSIGN: InfixBp = InfixBp::new_right(1);

    pub const POST_BRACKET: PostfixBp = PostfixBp::new(11);
    pub const POST_CALL: PostfixBp = PostfixBp::new(11);
    pub const POST_DOT: PostfixBp = PostfixBp::new(11);
}

pub mod ty_bp {
    use crate::base::syntax::PrefixBp;

    pub const PRE_POINTER: PrefixBp = PrefixBp::new(1);
    pub const PRE_FUNC_RETVAL: PrefixBp = PrefixBp::new(1);
}
