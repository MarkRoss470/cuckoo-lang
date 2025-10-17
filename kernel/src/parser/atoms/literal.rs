use crate::parser::atoms::char;
use crate::parser::combinators::modifiers::{ReparseExt, VerifyExt};
use crate::parser::combinators::repeat::Repeat1Ext;
use crate::parser::{ParseResult, Parser, parser};

pub(in crate::parser) fn nat_literal() -> impl Parser<Output = usize> {
    char()
        .verify(|c| c.is_numeric())
        .repeat_1()
        .reparse(parser(|input, _| {
            Some(("", ParseResult::new(input.parse().unwrap())))
        }))
}
