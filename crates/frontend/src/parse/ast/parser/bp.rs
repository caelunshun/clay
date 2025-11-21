pub mod expr_bp {
    use crate::base::syntax::{InfixBp, PostfixBp, PrefixBp};

    pub const PRE_NEG: PrefixBp = PrefixBp::new(9);
    pub const PRE_NOT: PrefixBp = PrefixBp::new(9);
    pub const PRE_REF: PrefixBp = PrefixBp::new(9);
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
    use crate::base::syntax::{PostfixBp, PrefixBp};

    pub const PRE_TY_REF: PrefixBp = PrefixBp::new(2);
    pub const POST_TY_OPT: PostfixBp = PostfixBp::new(1);
}
