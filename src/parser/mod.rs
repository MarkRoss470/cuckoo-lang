/// Puts a parser inside a closure to hide its type.
/// This allows parsers to be recursive, and keep `impl Parser` types smaller which helps compile times.
macro_rules! rec {
    ($parser: expr) => {{ $crate::parser::parser(move |input, context| $parser.parse(input, context)) }};
}

pub mod ast;
mod atoms;
mod combinators;

use std::io::Write;
use string_interner::symbol::SymbolU32;
use string_interner::DefaultBackend;

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

/// The type of the string interner
type Interner = string_interner::StringInterner<DefaultBackend>;
/// The key / symbol type used to compare / look up strings in the interner
type InternKey = SymbolU32;

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

trait Parser<T> {
    fn parse<'a>(&self, input: &'a str, context: ParseContext)
    -> Option<(&'a str, ParseResult<T>)>;
}

impl<T, F> Parser<T> for F
where
    F: for<'a> Fn(&'a str, ParseContext) -> Option<(&'a str, ParseResult<T>)>,
{
    fn parse<'a>(
        &self,
        input: &'a str,
        context: ParseContext,
    ) -> Option<(&'a str, ParseResult<T>)> {
        self(input, context)
    }
}

fn parser<T>(
    f: impl for<'a> Fn(&'a str, ParseContext) -> Option<(&'a str, ParseResult<T>)>,
) -> impl Parser<T> {
    f
}

#[allow(dead_code)]
fn todo<T>() -> impl Parser<T> {
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

trait PrettyPrint {
    fn pretty_print(&self, out: &mut dyn Write, context: PrettyPrintContext) -> std::io::Result<()>;
}