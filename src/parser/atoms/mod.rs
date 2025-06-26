pub mod whitespace;

use crate::parser::combinators::modifiers::{
    IgnoreValExt, MapExt, MapStrExt, ReparseExt, VerifyExt, VerifyStrExt,
};
use crate::parser::combinators::repeat::{Repeat0Ext, Repeat1Ext};
use crate::parser::combinators::sequence::SequenceExt;
use crate::parser::{
    InternKey, Interner, ParseResult, Parser, PrettyPrint, PrettyPrintContext, parser, todo,
};
use icu_properties::props::{IdContinue, IdStart, Math};
use icu_properties::{CodePointSetData, CodePointSetDataBorrowed};
use std::io::Write;

pub fn str_exact(s: &str) -> impl Parser<()> {
    parser(move |input, context| {
        input
            .strip_prefix(s)
            .map(|rest| (rest, ParseResult::new(())))
    })
}

fn char() -> impl Parser<char> {
    parser(move |input, context| {
        let mut chars = input.chars();
        let c = chars.next()?;
        Some((chars.as_str(), ParseResult::new(c)))
    })
}

fn intern() -> impl Parser<InternKey> {
    parser(|input, context| Some(("", ParseResult::new(context.interner.get_or_intern(input)))))
}

#[derive(Debug)]
pub struct Identifier(InternKey);

const ID_START_SET: CodePointSetDataBorrowed = CodePointSetData::new::<IdStart>();
const ID_CONTINUE_SET: CodePointSetDataBorrowed = CodePointSetData::new::<IdContinue>();

/// Sequences of characters which would be valid identifiers but are reserved for other purposes
const RESERVED_IDENTIFIERS: &[&str] = &["Type", "_", "data", "where"];

fn identifier_start() -> impl Parser<()> {
    char()
        .verify(|&c| c == '_' || ID_START_SET.contains(c))
        .ignore_val()
}

fn identifier_continue() -> impl Parser<()> {
    char()
        .verify(|&c| c == '_' || ID_CONTINUE_SET.contains(c))
        .ignore_val()
}

/// Parses an identifier, without the restriction that it can't be a keyword
fn identifier_like() -> impl Parser<Identifier> {
    (identifier_start(), identifier_continue().repeat_0())
        .sequence()
        .reparse(intern())
        .map(Identifier)
}

pub fn identifier() -> impl Parser<Identifier> {
    identifier_like().verify_str(|s| !RESERVED_IDENTIFIERS.binary_search(&s).is_ok())
}

pub fn keyword(kw: &str) -> impl Parser<()> {
    identifier_like().verify_str(move |s| s == kw).ignore_val()
}

#[derive(Debug)]
pub struct Operator(InternKey);

const MATH_SYMBOLS_SET: CodePointSetDataBorrowed = CodePointSetData::new::<Math>();

/// Sequences of characters which would be valid operators but are reserved for other types of syntax
const RESERVED_OPERATORS: &[&str] = &[".", ":", ":="];

fn is_operator_char(c: char) -> bool {
    match c {
        // These characters from the Basic Latin block are valid
        '!' | '#' | '$' | '%' | '&' | '*' | '-' | '.' | ':' | '?' | '@' | '\\' | '^' => true,
        // Characters in the Math Symbols set are also valid
        _ => MATH_SYMBOLS_SET.contains(c),
    }
}

fn operator_char() -> impl Parser<()> {
    char().verify(|c| is_operator_char(*c)).ignore_val()
}

/// Parses an operator, without the restriction that it can't be a reserved operator
pub fn operator_like() -> impl Parser<Operator> {
    operator_char().repeat_1().reparse(intern()).map(Operator)
}

pub fn operator() -> impl Parser<Operator> {
    operator_like().verify_str(|s| !RESERVED_OPERATORS.binary_search(&s).is_ok())
}

pub fn special_operator(op: &str) -> impl Parser<()> {
    operator_like().verify_str(move |s| s == op).ignore_val()
}

impl PrettyPrint for Identifier {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext,
    ) -> std::io::Result<()> {
        write!(out, "{}", context.interner.resolve(self.0).unwrap())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Checks that certain lists are sorted so that binary searches can be correctly performed on them
    #[test]
    fn test_sorted_lists() {
        assert!(RESERVED_IDENTIFIERS.is_sorted());
        assert!(RESERVED_OPERATORS.is_sorted());
    }
}
