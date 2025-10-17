pub mod ident;
pub mod literal;
pub mod whitespace;

use crate::parser::combinators::modifiers::{
    IgnoreValExt, MapExt, ReparseExt, VerifyExt, VerifyStrExt,
};
use crate::parser::combinators::repeat::Repeat1Ext;
use crate::parser::{ParseResult, Parser, parser};
use icu_properties::props::Math;
use icu_properties::{CodePointSetData, CodePointSetDataBorrowed};
use common::InternKey;

/// Parses exactly the given string once from the input
pub(in crate::parser) fn str_exact(s: &str) -> impl Parser<Output = ()> {
    parser(move |input, _| {
        input
            .strip_prefix(s)
            .map(|rest| (rest, ParseResult::new(())))
    })
}

/// Parses one character of input
fn char() -> impl Parser<Output = char> {
    parser(move |input, _| {
        let mut chars = input.chars();
        let c = chars.next()?;
        Some((chars.as_str(), ParseResult::new(c)))
    })
}

/// Consumes the entire input, adding it to the interner and returning the [`InternKey`]
fn intern() -> impl Parser<Output = InternKey> {
    parser(|input, context| Some(("", ParseResult::new(context.interner.get_or_intern(input)))))
}

#[derive(Debug)]
pub struct Operator(InternKey);

const MATH_SYMBOLS_SET: CodePointSetDataBorrowed = CodePointSetData::new::<Math>();

/// Sequences of characters which would be valid operators but are reserved for other types of syntax
const RESERVED_OPERATORS: &[&str] = &[".", ":", ":=", "=>", "|"];

fn is_operator_char(c: char) -> bool {
    match c {
        // These characters from the Basic Latin block are valid
        '!' | '#' | '$' | '%' | '&' | '*' | '-' | '.' | ':' | '?' | '@' | '\\' | '^' => true,
        // Characters in the Math Symbols set are also valid
        _ => MATH_SYMBOLS_SET.contains(c),
    }
}

fn operator_char() -> impl Parser<Output = ()> {
    char().verify(|c| is_operator_char(*c)).ignore_value()
}

/// Parses an operator, without the restriction that it can't be a reserved operator
fn operator_like() -> impl Parser<Output = Operator> {
    operator_char().repeat_1().reparse(intern()).map(Operator)
}

pub(super) fn operator() -> impl Parser<Output = Operator> {
    operator_like().verify_str(|s| !RESERVED_OPERATORS.binary_search(&s).is_ok())
}

pub(super) fn special_operator(op: &str) -> impl Parser<Output = ()> {
    debug_assert!(op.chars().all(is_operator_char));

    operator_like().verify_str(move |s| s == op).ignore_value()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::tests::{ParseAllExt, setup_context};

    /// Checks that certain lists are sorted so that binary searches can be correctly performed on them
    #[test]
    fn test_sorted_lists() {
        assert!(RESERVED_OPERATORS.is_sorted());
    }

    #[test]
    fn test_str_exact() {
        setup_context!(context);

        str_exact("test").parse_all("test", context.borrow());
        assert_eq!(
            str_exact("test")
                .parse("test string", context.borrow())
                .unwrap()
                .0,
            " string"
        );
        assert!(
            str_exact("test")
                .parse("not test", context.borrow())
                .is_none()
        );
    }
}
