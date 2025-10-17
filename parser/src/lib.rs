/// Puts a src inside a closure to hide its type.
/// This allows parsers to be recursive, and keep `impl Parser` types smaller which helps compile times.
#[macro_export]
macro_rules! rec {
    ($parser: expr) => {{ $crate::parser(move |input, context| $parser.parse(input, context)) }};
}

pub mod ast;
pub mod atoms;
pub mod combinators;

use common::{Interner, WithDiagnostics};
use std::io::Write;

#[cfg_attr(any(test, debug_assertions), derive(PartialEq))]
#[derive(Debug, Clone)]
pub enum ParseDiagnostic {}

pub type ParseResult<T> = WithDiagnostics<T, ParseDiagnostic>;

#[derive(Debug)]
pub struct ParseContext<'a> {
    interner: &'a mut Interner,
    indent_levels: usize,
}

impl<'a> ParseContext<'a> {
    pub fn new(interner: &'a mut Interner) -> Self {
        Self {
            interner,
            indent_levels: 0,
        }
    }

    pub fn interner(&mut self) -> &mut Interner {
        self.interner
    }
    
    pub fn indent_levels(&mut self) -> usize {
        self.indent_levels
    }
    
    pub fn borrow(&mut self) -> ParseContext<'_> {
        ParseContext {
            interner: &mut *self.interner,
            indent_levels: self.indent_levels,
        }
    }

    pub fn borrow_indented(&mut self) -> ParseContext<'_> {
        ParseContext {
            interner: &mut *self.interner,
            indent_levels: self.indent_levels + 1,
        }
    }
}

pub trait Parser {
    type Output;

    fn parse<'a>(
        &self,
        input: &'a str,
        context: ParseContext,
    ) -> Option<(&'a str, ParseResult<Self::Output>)>;
}

pub fn parser<T>(
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

#[allow(dead_code)]
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
        fn parse_all(&self, input: &str, context: ParseContext) -> Self::Output;
        fn parse_leaving(&self, input: &str, unparsed: &str, context: ParseContext)
        -> Self::Output;
    }

    impl<P: Parser> ParseAllExt for P {
        fn parse_all(&self, input: &str, context: ParseContext) -> Self::Output {
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
            context: ParseContext,
        ) -> Self::Output {
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
