use crate::parse::{
    ast::{AstItemModuleContents, item::parse_mod_contents},
    token::{TokenCursor, TokenGroup, TokenParser},
};

pub type P<'a, 'g> = &'a mut TokenParser<'g>;
pub type C<'a, 'g> = &'a mut TokenCursor<'g>;

pub fn parse_file(tokens: &TokenGroup) -> AstItemModuleContents {
    let mut p = TokenParser::new(tokens);

    parse_mod_contents(&mut p)
}
