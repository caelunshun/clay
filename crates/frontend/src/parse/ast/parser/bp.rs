// FIXME

pub mod expr_bp {
    use crate::base::syntax::{InfixBp, PostfixBp, PrefixBp};

    // `-exp`
    pub const PRE_NEG: PrefixBp = PrefixBp::new(9);

    // `!exp`
    pub const PRE_NOT: PrefixBp = PrefixBp::new(9);

    // `&exp`
    pub const PRE_REF: PrefixBp = PrefixBp::new(9);

    // `return exp;`
    pub const PRE_RETURN: PrefixBp = PrefixBp::new(1);

    // `break exp;`
    pub const PRE_BREAK: PrefixBp = PrefixBp::new(1);

    // `let pat = expr`
    pub const PRE_LET: PrefixBp = PrefixBp::new(8);

    // `exp + exp`
    pub const INFIX_ADD: InfixBp = InfixBp::new_left(2);

    // `exp - exp`
    pub const INFIX_SUB: InfixBp = InfixBp::new_left(2);

    // `exp * exp`
    pub const INFIX_MUL: InfixBp = InfixBp::new_left(3);

    // `exp / exp`
    pub const INFIX_DIV: InfixBp = InfixBp::new_left(3);

    // `exp % exp`
    pub const INFIX_REM: InfixBp = InfixBp::new_left(3);

    // `exp == exp`
    pub const INFIX_EQ: InfixBp = InfixBp::new_left(3);

    // `exp != exp`
    pub const INFIX_NEQ: InfixBp = InfixBp::new_left(3);

    // `exp < exp`
    pub const INFIX_LT: InfixBp = InfixBp::new_left(3);

    // `exp <= exp`
    pub const INFIX_LTE: InfixBp = InfixBp::new_left(3);

    // `exp > exp`
    pub const INFIX_GT: InfixBp = InfixBp::new_left(3);

    // `exp >= exp`
    pub const INFIX_GTE: InfixBp = InfixBp::new_left(3);

    // `exp & exp`
    pub const INFIX_BIT_AND: InfixBp = InfixBp::new_left(3);

    // `exp | exp`
    pub const INFIX_BIT_OR: InfixBp = InfixBp::new_left(3);

    // `exp ^ exp`
    pub const INFIX_BIT_XOR: InfixBp = InfixBp::new_left(3);

    // `exp << exp`
    pub const INFIX_BIT_SHL: InfixBp = InfixBp::new_left(3);

    // `exp >> exp`
    pub const INFIX_BIT_SHR: InfixBp = InfixBp::new_left(3);

    // `exp && exp`
    pub const INFIX_LOGICAL_AND: InfixBp = InfixBp::new_left(3);

    // `exp || exp`
    pub const INFIX_LOGICAL_OR: InfixBp = InfixBp::new_left(3);

    // `exp = exp`
    pub const INFIX_ASSIGN: InfixBp = InfixBp::new_right(1);

    // `exp += exp`
    pub const INFIX_ASSIGN_ADD: InfixBp = InfixBp::new_right(1);

    // `exp -= exp`
    pub const INFIX_ASSIGN_SUB: InfixBp = InfixBp::new_right(1);

    // `exp *= exp`
    pub const INFIX_ASSIGN_MUL: InfixBp = InfixBp::new_right(1);

    // `exp /= exp`
    pub const INFIX_ASSIGN_DIV: InfixBp = InfixBp::new_right(1);

    // `exp %= exp`
    pub const INFIX_ASSIGN_REM: InfixBp = InfixBp::new_right(1);

    // `exp ^= exp`
    pub const INFIX_ASSIGN_BIT_XOR: InfixBp = InfixBp::new_right(1);

    // `exp &= exp`
    pub const INFIX_ASSIGN_BIT_AND: InfixBp = InfixBp::new_right(1);

    // `exp |= exp`
    pub const INFIX_ASSIGN_BIT_OR: InfixBp = InfixBp::new_right(1);

    // `exp <<= exp`
    pub const INFIX_ASSIGN_SHL: InfixBp = InfixBp::new_right(1);

    // `exp >>= exp`
    pub const INFIX_ASSIGN_SHR: InfixBp = InfixBp::new_right(1);

    // `.. (exp)?`
    pub const PRE_RANGE: PrefixBp = PrefixBp::new(1);

    // `exp .. (exp)?`
    pub const INFIX_RANGE: InfixBp = InfixBp::new_right(1);

    // `exp[exp]`
    pub const POST_BRACKET: PostfixBp = PostfixBp::new(11);

    // `exp(...)`
    pub const POST_CALL: PostfixBp = PostfixBp::new(11);

    // `exp.name`
    pub const POST_DOT: PostfixBp = PostfixBp::new(11);
}

pub mod ty_bp {
    use crate::base::syntax::{PostfixBp, PrefixBp};

    pub const PRE_TY_REF: PrefixBp = PrefixBp::new(2);
    pub const POST_TY_OPT: PostfixBp = PostfixBp::new(1);
}
