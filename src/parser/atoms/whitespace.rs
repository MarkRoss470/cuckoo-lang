use crate::parser::atoms::{char, str_exact};
use crate::parser::combinators::alt::AltExt;
use crate::parser::combinators::modifiers::{IgnoreValExt, VerifyExt};
use crate::parser::combinators::repeat::{RepeatExactExt, Repeat0Ext, RepeatWhileExt};
use crate::parser::combinators::sequence::SequenceExt;
use crate::parser::{Parser, parser, todo};

/// Parses exactly n levels of indentation
fn indent_exact(n: usize) -> impl Parser<()> {
    str_exact("  ").repeat_exact(n).ignore_val()
}

/// Parses the current level of indentation, taken from the context
fn current_indent() -> impl Parser<()> {
    parser(|input, context| indent_exact(context.indent_levels).parse(input, context))
}

/// Parses a newline character followed by the appropriate indentation  
pub fn newline_and_indent() -> impl Parser<()> {
    (str_exact("\n"), current_indent()).sequence().ignore_val()
}

/// Parses a single whitespace character that's not a newline
fn non_newline_whitespace() -> impl Parser<()> {
    char()
        .verify(|c| c.is_whitespace() && *c != '\n')
        .ignore_val()
}

/// Parses comments
fn comment() -> impl Parser<()> {
    (
        str_exact("--"),
        char().repeat_0_while(|c| *c != '\n'),
        newline_and_indent(),
    )
        .sequence()
        .ignore_val()
}

/// Parses whitespace
pub fn whitespace() -> impl Parser<()> {
    (newline_and_indent(), non_newline_whitespace(), comment())
        .alt()
        .repeat_0()
        .ignore_val()
}

/// Runs the given parser in an indented block
fn in_block<T, P: Parser<T>>(p: P) -> impl Parser<T> {
    parser(move |input, mut context| p.parse(input, context.borrow_indented()))
}

pub trait InBlockExt<T>: Parser<T> {
    fn in_block(self) -> impl Parser<T>;
}

impl<T, P: Parser<T>> InBlockExt<T> for P {
    fn in_block(self) -> impl Parser<T> {
        in_block(self)
    }
}
