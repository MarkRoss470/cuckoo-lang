/// Puts a src inside a closure to hide its type.
/// This allows parsers to be recursive, and keep `impl Parser` types smaller which helps compile times.
#[macro_export]
macro_rules! rec {
    ($parser: expr) => {{ $crate::parser(move |input, context| $parser.parse(input, context)) }};
}

pub mod ast;
pub mod atoms;
mod combinators;
pub mod error;

use crate::error::{ParseDiagnostic, ParseDiagnosticKind, SourceLocation, Span};
use common::{Interner, WithDiagnostics};
use std::io::Write;
use std::iter;

type ParseResult<T> = WithDiagnostics<T, ParseDiagnostic>;

#[derive(Debug)]
pub struct SourceFile<'a> {
    source: &'a str,
    /// The byte offsets into `source` of every newline
    line_start_offsets: Vec<usize>,
}

impl<'a> SourceFile<'a> {
    pub fn new(source: &'a str) -> Self {
        let line_start_offsets = iter::once(0)
            .chain(
                source
                    .bytes()
                    .enumerate()
                    .filter(|(_, c)| *c == b'\n')
                    .map(|(i, _)| i),
            )
            .collect();

        Self {
            source,
            line_start_offsets,
        }
    }

    pub fn location_of_offset(&self, byte_offset: usize) -> SourceLocation {
        let line = self
            .line_start_offsets
            .partition_point(|line_start| *line_start <= byte_offset);

        SourceLocation {
            byte_offset,
            line,
            column: byte_offset - self.line_start_offsets[line - 1] + 1,
        }
    }
}

#[derive(Debug)]
struct ParseContext<'a> {
    source: &'a SourceFile<'a>,
    interner: &'a mut Interner,
    indent_levels: usize,
}

impl<'a> ParseContext<'a> {
    fn new(interner: &'a mut Interner, source: &'a SourceFile<'a>) -> Self {
        Self {
            source,
            interner,
            indent_levels: 0,
        }
    }

    fn interner(&mut self) -> &mut Interner {
        self.interner
    }

    fn indent_levels(&mut self) -> usize {
        self.indent_levels
    }

    fn borrow(&mut self) -> ParseContext<'_> {
        ParseContext {
            source: self.source,
            interner: &mut *self.interner,
            indent_levels: self.indent_levels,
        }
    }

    fn borrow_indented(&mut self) -> ParseContext<'_> {
        ParseContext {
            source: self.source,
            interner: &mut *self.interner,
            indent_levels: self.indent_levels + 1,
        }
    }

    fn location_of(&self, rest: &str) -> SourceLocation {
        self.source
            .location_of_offset(self.source.source.len() - rest.len())
    }

    fn diagnostic_at(&self, rest: &str, kind: ParseDiagnosticKind) -> ParseDiagnostic {
        ParseDiagnostic {
            location: Span::point(self.location_of(rest)),
            kind,
        }
    }
}

trait Parser {
    type Output;

    fn parse<'a>(
        &self,
        input: &'a str,
        context: ParseContext,
    ) -> Option<(&'a str, ParseResult<Self::Output>)>;
}

fn parser<T>(
    f: impl for<'a> Fn(&'a str, ParseContext) -> Option<(&'a str, ParseResult<T>)>,
) -> impl Parser<Output = T> {
    struct FnParser<T, F: for<'a> Fn(&'a str, ParseContext) -> Option<(&'a str, ParseResult<T>)>>(
        F,
    );

    impl<T, F: for<'a> Fn(&'a str, ParseContext) -> Option<(&'a str, ParseResult<T>)>> Parser
        for FnParser<T, F>
    {
        type Output = T;

        fn parse<'a>(
            &self,
            input: &'a str,
            context: ParseContext,
        ) -> Option<(&'a str, ParseResult<Self::Output>)> {
            self.0(input, context)
        }
    }

    FnParser(f)
}

#[expect(dead_code)]
fn todo<T>() -> impl Parser<Output = T> {
    parser(|_, _| todo!())
}

#[derive(Debug, Copy, Clone)]
struct PrettyPrintContext<'a> {
    interner: &'a Interner,
    indent_levels: usize,
}

impl<'a> PrettyPrintContext<'a> {
    fn borrow_indented(&self) -> PrettyPrintContext<'_> {
        PrettyPrintContext {
            interner: &self.interner,
            indent_levels: self.indent_levels + 1,
        }
    }

    fn newline(&self, out: &mut dyn Write) -> std::io::Result<()> {
        writeln!(out)?;
        for _ in 0..self.indent_levels {
            write!(out, "  ")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! setup_context {
        ($context: ident) => {
            let mut interner = ::common::Interner::new();
            #[allow(unused_mut)]
            let mut $context = $crate::ParseContext {
                interner: &mut interner,
                indent_levels: 0,
            };
        };
    }

    pub(crate) use setup_context;

    pub(crate) trait ParseAllExt: Parser {
        fn parse_all(&self, input: &str, interner: &mut Interner) -> Self::Output;
        fn parse_leaving(
            &self,
            input: &str,
            unparsed: &str,
            interner: &mut Interner,
        ) -> Self::Output;
    }

    impl<P: Parser> ParseAllExt for P {
        fn parse_all(&self, input: &str, interner: &mut Interner) -> Self::Output {
            let context = ParseContext::new(interner, input);

            match self.parse(input, context) {
                None => panic!("Parser should have recognised input"),
                Some((rest, val)) => {
                    if !rest.is_empty() {
                        panic!(
                            "Parser should have consumed the entire input, but it left '{rest}' unparsed."
                        );
                    }

                    val.unwrap()
                }
            }
        }

        fn parse_leaving(
            &self,
            input: &str,
            unparsed: &str,
            interner: &mut Interner,
        ) -> Self::Output {
            let context = ParseContext::new(interner, input);

            match self.parse(input, context) {
                None => panic!("Parser should have recognised input"),
                Some((rest, val)) => {
                    if rest != unparsed {
                        panic!(
                            "Parser should have left {unparsed:?} unparsed, but it left {rest:?}."
                        );
                    }

                    val.unwrap()
                }
            }
        }
    }
}
