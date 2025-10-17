use crate::atoms::char;
use crate::combinators::modifiers::{ReparseExt, VerifyExt};
use crate::combinators::repeat::Repeat1Ext;
use crate::{ParseResult, Parser, parser};

pub fn nat_literal() -> impl Parser<Output = usize> {
    char()
        .verify(|c| c.is_numeric())
        .repeat_1()
        .reparse(parser(|input, _| {
            Some(("", ParseResult::new(input.parse().unwrap())))
        }))
}
