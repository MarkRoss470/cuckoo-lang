use crate::atoms::whitespace::SurroundWhitespaceExt;
use crate::combinators::repeat::Repeat0Ext;
use crate::error::ParseDiagnostic;
use crate::{ParseContext, SourceFile};
use crate::{Parser, PrettyPrintContext};
use common::{Interner, PrettyPrint, WithDiagnostics};
use item::{Item, item};

pub mod item;
pub mod term;

#[derive(Debug)]
pub struct Ast {
    pub items: Vec<Item>,
}

pub fn parse_file(interner: &mut Interner, content: &str) -> WithDiagnostics<Ast, ParseDiagnostic> {
    let source = SourceFile::new(content);
    let context = ParseContext {
        source: &source,
        interner,
        indent_levels: 0,
    };

    let (rest, res) = item()
        .surround_whitespace()
        .repeat_0()
        .parse(content, context)
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
    use crate::ast::term::{Term, term};
    use crate::ParseResult;

    pub fn parse_term(interner: &mut Interner, source: &str) -> ParseResult<Term> {
        let source_file = SourceFile::new(source);
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
