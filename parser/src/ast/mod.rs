use crate::ast::item::import::import_statement;
use crate::atoms::whitespace::SurroundWhitespaceExt;
use crate::combinators::modifiers::MapExt;
use crate::combinators::repeat::{Repeat0Ext, Repeat0FlatteningExt};
use crate::combinators::tuples::HomogeneousTupleExt;
use crate::error::{ParseDiagnostic, ParseDiagnosticKind, SourceLocation, Span};
use crate::{ParseContext, Source, SourceFile, SourceFromFileError};
use crate::{Parser, PrettyPrintContext};
use common::{Interner, PrettyPrint, WithDiagnostics};
use item::{Item, item};
use std::path::PathBuf;
use std::rc::Rc;

pub mod item;
pub mod term;

#[derive(Debug)]
pub struct Ast {
    pub items: Vec<Item>,
}

pub fn parse_file(
    interner: &mut Interner,
    source: &SourceFile,
) -> WithDiagnostics<Ast, ParseDiagnostic> {
    let context = ParseContext {
        source: &source,
        interner,
        indent_levels: 0,
    };

    // TODO: move import statement resolution to the elaborator
    let (rest, res) = (import_statement(), item().map(|i| vec![i]))
        .alt()
        .surround_whitespace()
        .repeat_0_flattening()
        .parse(&source.content, context)
        .unwrap();

    if !rest.is_empty() {
        panic!("Some content unparsed: {rest:?}");
    }

    res.map(|items| Ast { items })
}

impl Ast {
    pub fn pretty_print(&self, interner: &Interner) {
        let context = PrettyPrintContext {
            interner,
            indent_levels: 0,
        };

        let mut stdout = std::io::stdout().lock();

        for item in &self.items {
            item.pretty_print(&mut stdout, context).unwrap();
        }
    }
}

#[cfg(any(test, feature = "test-utils"))]
pub mod tests {
    use super::*;
    use crate::ParseResult;
    use crate::ast::term::{Term, term};

    pub fn parse_term(interner: &mut Interner, source: &str) -> ParseResult<Term> {
        let source_file = SourceFile::test_source(source);
        let context = ParseContext {
            source: &source_file,
            interner,
            indent_levels: 0,
        };

        let (rest, term) = term()
            .parse(source, context)
            .expect("Term should have parsed");
        assert!(rest.is_empty(), "Leftover text when parsing term: {rest:?}");

        term
    }
}
