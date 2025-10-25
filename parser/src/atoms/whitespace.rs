use crate::atoms::{char, str_exact};
use crate::combinators::modifiers::{IgnoreValExt, VerifyExt};
use crate::combinators::repeat::{Repeat0Ext, RepeatExactExt, RepeatWhileExt};
use crate::combinators::tuples::{HeterogeneousTupleExt, HomogeneousTupleExt};
use crate::{Parser, parser};

/// Parses exactly n levels of indentation
fn indent_exact(n: usize) -> impl Parser<Output = ()> {
    str_exact("  ").repeat_exact(n).ignore_value()
}

/// Parses the current level of indentation, taken from the context
fn current_indent() -> impl Parser<Output = ()> {
    parser(|input, context| indent_exact(context.indent_levels).parse(input, context))
}

/// Parses a sequence of newline characters with whitespace, followed by the appropriate indentation  
pub(crate) fn newlines_and_indent() -> impl Parser<Output = ()> {
    rec!(
        (
            str_exact("\n"),
            (non_newline_whitespace(), str_exact("\n"))
                .sequence()
                .repeat_0(),
            current_indent(),
        )
            .sequence()
            .ignore_value()
    )
}

/// Parses a single whitespace character that's not a newline
fn single_non_newline_whitespace() -> impl Parser<Output = ()> {
    char()
        .verify(|c| c.is_whitespace() && *c != '\n')
        .ignore_value()
}

/// Parses comments
fn comment() -> impl Parser<Output = ()> {
    rec!(
        (str_exact("--"), char().repeat_0_while(|c| *c != '\n'))
            .sequence()
            .ignore_value()
    )
}

/// Parses whitespace
pub(crate) fn whitespace() -> impl Parser<Output = ()> {
    rec!(
        (
            newlines_and_indent(),
            single_non_newline_whitespace(),
            comment(),
        )
            .alt()
            .repeat_0()
            .ignore_value()
    )
}

pub(crate) fn non_newline_whitespace() -> impl Parser<Output = ()> {
    rec!(
        (single_non_newline_whitespace(), comment())
            .alt()
            .repeat_0()
            .ignore_value()
    )
}

pub(crate) trait SurroundWhitespaceExt: Parser {
    fn surround_whitespace(self) -> impl Parser<Output = Self::Output>;
}

impl<P: Parser> SurroundWhitespaceExt for P {
    fn surround_whitespace(self) -> impl Parser<Output = Self::Output> {
        (whitespace(), self, whitespace()).combine(|(_, v, _)| v)
    }
}

pub(crate) trait InBlockExt: Parser {
    /// Runs the given src in an indented block
    fn in_block(self) -> impl Parser<Output = Self::Output>;
}

impl<P: Parser> InBlockExt for P {
    fn in_block(self) -> impl Parser<Output = Self::Output> {
        parser(move |input, mut context| self.parse(input, context.borrow_indented()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::ParserTestExt;
    use common::Interner;

    #[test]
    fn test_newline_and_indent() {
        let mut interner = Interner::new();

        newlines_and_indent().assert_no_match("   a", &mut interner);

        newlines_and_indent().parse_leaving("\n  a", "  a", &mut interner);
        newlines_and_indent().parse_leaving("\n\n  a", "  a", &mut interner);
        newlines_and_indent().parse_leaving("\n-- a comment\n  a", "  a", &mut interner);
        newlines_and_indent().parse_leaving(
            "\n                         -- a comment\n  a",
            "  a",
            &mut interner,
        );
        newlines_and_indent().parse_leaving(
            "\n                         not a comment\n  a",
            "                         not a comment\n  a",
            &mut interner,
        );
        newlines_and_indent().parse_leaving("\n  \n  a", "  a", &mut interner);

        newlines_and_indent().assert_no_match_with_indent(1, "\na", &mut interner);
        newlines_and_indent().assert_no_match_with_indent(1, "\n    \na", &mut interner);
        newlines_and_indent().assert_no_match_with_indent(
            1,
            "\n    \n--a comment\n",
            &mut interner,
        );

        newlines_and_indent().parse_leaving_with_indent(1, "\n  a", "a", &mut interner);
        newlines_and_indent().parse_leaving_with_indent(1, "\n\n  a", "a", &mut interner);
        newlines_and_indent().parse_leaving_with_indent(
            1,
            "\n-- a comment\n  a",
            "a",
            &mut interner,
        );
        newlines_and_indent().parse_leaving_with_indent(
            1,
            "\n                         -- a comment\n  a",
            "a",
            &mut interner,
        );
        newlines_and_indent().parse_leaving_with_indent(
            1,
            "\n                         not a comment\n  a",
            "                       not a comment\n  a",
            &mut interner,
        );
        newlines_and_indent().parse_leaving_with_indent(1, "\n  \n  a", "a", &mut interner);
    }

    #[test]
    fn test_whitespace() {
        let mut interner = Interner::new();

        whitespace().parse_leaving("a", "a", &mut interner);
        whitespace().parse_leaving("  a", "a", &mut interner);
        whitespace().parse_leaving("\n\n\ta", "a", &mut interner);
        whitespace().parse_leaving("\n  \t\t   -- a comment\n  a", "a", &mut interner);

        whitespace().parse_leaving_with_indent(1, "a", "a", &mut interner);
        whitespace().parse_leaving_with_indent(1, "  a", "a", &mut interner);
        // `whitespace` still matches this but doesn't consume the whitespace
        whitespace().parse_leaving_with_indent(1, "\n\na", "\n\na", &mut interner);
        // Whereas this one has the correct indent before the `a` so the whitespace is consumed
        whitespace().parse_leaving_with_indent(1, "\n\n  a", "a", &mut interner);
        whitespace().parse_leaving_with_indent(1, "\n       -- a comment\n  a", "a", &mut interner);
    }
}
