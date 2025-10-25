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
use std::fmt::{Display, Formatter};
use std::io::Write;
use std::path::PathBuf;
use std::rc::Rc;
use std::string::FromUtf8Error;
use std::{fs, io, iter};

type ParseResult<T> = WithDiagnostics<T, ParseDiagnostic>;

#[derive(Debug, Clone, PartialEq)]
pub enum Source {
    File(PathBuf),
    TestSource,
}

#[derive(Debug)]
pub struct SourceFile {
    source: Rc<Source>,
    content: String,
    /// The byte offsets into `source` of every newline
    line_start_offsets: Vec<usize>,
}

#[derive(Debug)]
pub enum SourceFromFileError {
    IoError(io::Error),
    FromUtf8Error(FromUtf8Error),
}

impl From<io::Error> for SourceFromFileError {
    fn from(value: io::Error) -> Self {
        Self::IoError(value)
    }
}

impl From<FromUtf8Error> for SourceFromFileError {
    fn from(value: FromUtf8Error) -> Self {
        Self::FromUtf8Error(value)
    }
}

impl Display for SourceFromFileError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            SourceFromFileError::IoError(e) => write!(f, "{e}"),
            SourceFromFileError::FromUtf8Error(e) => write!(f, "{e}"),
        }
    }
}

impl SourceFile {
    pub fn from_file(path: PathBuf) -> Result<Self, SourceFromFileError> {
        let content = fs::read(&path)?;
        let content = String::from_utf8(content)?;

        let line_start_offsets = Self::calculate_line_start_offsets(&content);

        Ok(Self {
            source: Rc::new(Source::File(path)),
            content,
            line_start_offsets,
        })
    }

    pub fn test_source(content: &str) -> Self {
        Self {
            source: Rc::new(Source::TestSource),
            content: content.to_string(),
            line_start_offsets: Self::calculate_line_start_offsets(content),
        }
    }

    fn calculate_line_start_offsets(source: &str) -> Vec<usize> {
        let line_start_offsets = iter::once(0)
            .chain(
                source
                    .bytes()
                    .enumerate()
                    .filter(|(_, c)| *c == b'\n')
                    .map(|(i, _)| i + 1),
            )
            .collect();
        line_start_offsets
    }

    pub fn location_of_offset(&self, byte_offset: usize) -> Span {
        let line = self
            .line_start_offsets
            .partition_point(|line_start| *line_start <= byte_offset);

        let location = SourceLocation {
            byte_offset,
            line,
            column: byte_offset - self.line_start_offsets[line - 1] + 1,
        };

        Span {
            source: self.source.clone(),
            start: location,
            end: location,
        }
    }
}

#[derive(Debug)]
struct ParseContext<'a> {
    source: &'a SourceFile,
    interner: &'a mut Interner,
    indent_levels: usize,
}

impl<'a> ParseContext<'a> {
    fn new(interner: &'a mut Interner, source: &'a SourceFile) -> Self {
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

    fn location_of(&self, rest: &str) -> Span {
        self.source
            .location_of_offset(self.source.content.len() - rest.len())
    }

    fn diagnostic_at(&self, rest: &str, kind: ParseDiagnosticKind) -> ParseDiagnostic {
        ParseDiagnostic {
            location: self.location_of(rest),
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

    pub(crate) trait ParserTestExt: Parser {
        fn assert_no_match_with_indent(&self, indent: usize, input: &str, interner: &mut Interner);
        fn assert_no_match(&self, input: &str, interner: &mut Interner);
        fn parse_all(&self, input: &str, interner: &mut Interner) -> Self::Output;
        fn parse_leaving_with_indent(
            &self,
            indent: usize,
            input: &str,
            unparsed: &str,
            interner: &mut Interner,
        ) -> Self::Output;
        fn parse_leaving(
            &self,
            input: &str,
            unparsed: &str,
            interner: &mut Interner,
        ) -> Self::Output;
    }

    impl<P: Parser> ParserTestExt for P {
        fn assert_no_match_with_indent(&self, indent: usize, input: &str, interner: &mut Interner) {
            let source = SourceFile::test_source(input);
            let mut context = ParseContext::new(interner, &source);
            context.indent_levels = indent;

            match self.parse(input, context) {
                None => {}
                Some(_) => {
                    panic!("Parser should not have matched")
                }
            }
        }

        fn assert_no_match(&self, input: &str, interner: &mut Interner) {
            self.assert_no_match_with_indent(0, input, interner);
        }

        fn parse_all(&self, input: &str, interner: &mut Interner) -> Self::Output {
            let source = SourceFile::test_source(input);
            let context = ParseContext::new(interner, &source);

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

        fn parse_leaving_with_indent(
            &self,
            indent: usize,
            input: &str,
            unparsed: &str,
            interner: &mut Interner,
        ) -> Self::Output {
            let source = SourceFile::test_source(input);
            let mut context = ParseContext::new(interner, &source);
            context.indent_levels = indent;

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

        fn parse_leaving(
            &self,
            input: &str,
            unparsed: &str,
            interner: &mut Interner,
        ) -> Self::Output {
            self.parse_leaving_with_indent(0, input, unparsed, interner)
        }
    }

    #[test]
    fn test_location_of() {
        let source = "here is some text.\nthis is a new line.\n   \n   Here is another.";
        let file = SourceFile::test_source(source);

        assert_eq!(file.location_of_offset(0).start.line, 1);
        assert_eq!(file.location_of_offset(0).start.column, 1);
        assert_eq!(file.location_of_offset(10).start.line, 1);
        assert_eq!(file.location_of_offset(10).start.column, 11);
        assert_eq!(file.location_of_offset(17).start.line, 1);
        assert_eq!(file.location_of_offset(17).start.column, 18);
        assert_eq!(file.location_of_offset(18).start.line, 1);
        assert_eq!(file.location_of_offset(18).start.column, 19);
        assert_eq!(file.location_of_offset(19).start.line, 2);
        assert_eq!(file.location_of_offset(19).start.column, 1);
        assert_eq!(file.location_of_offset(25).start.line, 2);
        assert_eq!(file.location_of_offset(25).start.column, 7);
        assert_eq!(file.location_of_offset(38).start.line, 2);
        assert_eq!(file.location_of_offset(38).start.column, 20);
        assert_eq!(file.location_of_offset(39).start.line, 3);
        assert_eq!(file.location_of_offset(39).start.column, 1);
        assert_eq!(file.location_of_offset(61).start.line, 4);
        assert_eq!(file.location_of_offset(61).start.column, 19);
    }
}
