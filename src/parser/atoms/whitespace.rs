use crate::parser::atoms::{char, str_exact};
use crate::parser::combinators::modifiers::{IgnoreValExt, VerifyExt};
use crate::parser::combinators::repeat::{Repeat0Ext, RepeatExactExt, RepeatWhileExt};
use crate::parser::combinators::tuples::{HeterogeneousTupleExt, HomogeneousTupleExt};
use crate::parser::{Parser, parser, todo};

/// Parses exactly n levels of indentation
fn indent_exact(n: usize) -> impl Parser<Output = ()> {
    str_exact("  ").repeat_exact(n).ignore_value()
}

/// Parses the current level of indentation, taken from the context
fn current_indent() -> impl Parser<Output = ()> {
    parser(|input, context| indent_exact(context.indent_levels).parse(input, context))
}

/// Parses a newline character followed by the appropriate indentation  
pub fn newline_and_indent() -> impl Parser<Output = ()> {
    (str_exact("\n"), current_indent())
        .sequence()
        .ignore_value()
}

/// Parses a single whitespace character that's not a newline
fn single_non_newline_whitespace() -> impl Parser<Output = ()> {
    char()
        .verify(|c| c.is_whitespace() && *c != '\n')
        .ignore_value()
}

/// Parses comments
fn comment() -> impl Parser<Output = ()> {
    (str_exact("--"), char().repeat_0_while(|c| *c != '\n'))
        .sequence()
        .ignore_value()
}

/// Parses whitespace
pub fn whitespace() -> impl Parser<Output = ()> {
    (
        newline_and_indent(),
        single_non_newline_whitespace(),
        comment(),
    )
        .alt()
        .repeat_0()
        .ignore_value()
}

pub fn non_newline_whitespace() -> impl Parser<Output = ()> {
    (single_non_newline_whitespace(), comment())
        .alt()
        .repeat_0()
        .ignore_value()
}

pub trait SurroundWhitespaceExt: Parser {
    fn surround_whitespace(self) -> impl Parser<Output = Self::Output>;
}

impl<P: Parser> SurroundWhitespaceExt for P {
    fn surround_whitespace(self) -> impl Parser<Output = Self::Output> {
        (whitespace(), self, whitespace()).combine(|(_, v, _)| v)
    }
}

pub trait InBlockExt: Parser {
    /// Runs the given parser in an indented block
    fn in_block(self) -> impl Parser<Output = Self::Output>;
}

impl<P: Parser> InBlockExt for P {
    fn in_block(self) -> impl Parser<Output = Self::Output> {
        parser(move |input, mut context| self.parse(input, context.borrow_indented()))
    }
}
