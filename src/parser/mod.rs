/// Puts a parser inside a closure to hide its type.
/// This allows parsers to be recursive, and keep `impl Parser` types smaller which helps compile times.
macro_rules! rec {
    ($parser: expr) => {{ $crate::parser::parser(move |input, context| $parser.parse(input, context)) }};
}

pub mod ast;
pub mod atoms;
mod combinators;

use crate::parser::atoms::ident::Identifier;
use std::io::Write;
use string_interner::symbol::SymbolU32;
use string_interner::{DefaultBackend, StringInterner};

#[derive(Debug)]
pub enum ParseError {}

#[derive(Debug)]
pub struct ParseResult<T> {
    pub value: T,
    pub errors: Vec<ParseError>,
    pub warnings: Vec<ParseError>,
}

impl<T> ParseResult<T> {
    fn new(value: T) -> Self {
        Self {
            value,
            errors: vec![],
            warnings: vec![],
        }
    }

    fn take_errors_from<U>(&mut self, mut other: ParseResult<U>) -> U {
        self.errors.append(&mut other.errors);
        self.warnings.append(&mut other.warnings);
        other.value
    }

    fn with_errors_from<U>(mut self, other: ParseResult<U>) -> Self {
        self.take_errors_from(other);
        self
    }

    fn with_value<U>(self, value: U) -> ParseResult<U> {
        ParseResult {
            value,
            errors: self.errors,
            warnings: self.warnings,
        }
    }

    fn map<U, F: FnOnce(T) -> U>(self, f: F) -> ParseResult<U> {
        let v = f(self.value);

        ParseResult {
            value: v,
            errors: self.errors,
            warnings: self.warnings,
        }
    }
}

/// The key / symbol type used to compare / look up strings in the interner
pub type InternKey = SymbolU32;

/// The parser's string interner type
#[derive(Debug)]
pub struct Interner {
    interner: StringInterner<DefaultBackend>,
    /// The identifier corresponding to the 'rec' keyword
    kw_rec: Identifier,
}

impl Interner {
    pub fn new() -> Self {
        let mut interner = StringInterner::new();
        let kw_rec = Identifier(interner.get_or_intern("rec"));
        Self { interner, kw_rec }
    }

    pub fn get_or_intern(&mut self, string: &str) -> InternKey {
        self.interner.get_or_intern(string)
    }

    pub fn resolve(&self, symbol: InternKey) -> Option<&str> {
        self.interner.resolve(symbol)
    }

    pub fn kw_rec(&self) -> Identifier {
        self.kw_rec
    }
}

#[derive(Debug)]
struct ParseContext<'a> {
    interner: &'a mut Interner,
    indent_levels: usize,
}

impl<'a> ParseContext<'a> {
    fn borrow(&mut self) -> ParseContext {
        ParseContext {
            interner: &mut *self.interner,
            indent_levels: self.indent_levels,
        }
    }

    fn borrow_indented(&mut self) -> ParseContext {
        ParseContext {
            interner: &mut *self.interner,
            indent_levels: self.indent_levels + 1,
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
    fn borrow_indented(&self) -> PrettyPrintContext {
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

pub trait PrettyPrint<C> {
    fn pretty_print(&self, out: &mut dyn Write, context: C) -> std::io::Result<()>;
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! setup_context {
        ($context: ident) => {
            let mut interner = $crate::parser::Interner::new();
            #[allow(unused_mut)]
            let mut $context = $crate::parser::ParseContext {
                interner: &mut interner,
                indent_levels: 0,
            };
        };
    }

    pub(in crate::parser) use setup_context;

    pub(in crate::parser) trait ParseAllExt: Parser {
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

                    assert!(val.warnings.is_empty() && val.errors.is_empty());

                    val.value
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

                    assert!(val.warnings.is_empty() && val.errors.is_empty());

                    val.value
                }
            }
        }
    }
}
