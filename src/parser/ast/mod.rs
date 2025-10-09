use crate::parser::PrettyPrint;
use crate::parser::atoms::whitespace::SurroundWhitespaceExt;
use crate::parser::combinators::repeat::Repeat0Ext;
use crate::parser::combinators::tuples::HeterogeneousTupleExt;
use crate::parser::{Interner, ParseContext, ParseResult};
use crate::parser::{Parser, PrettyPrintContext};
use item::{Item, item};

pub mod item;
pub mod term;

#[derive(Debug)]
pub struct Ast {
    pub items: Vec<Item>,
}

pub fn parse_file(content: &str) -> ParseResult<(Interner, Ast)> {
    let mut interner = Interner::new();
    let context = ParseContext {
        interner: &mut interner,
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

    res.map(|items| (interner, Ast { items }))
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

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::parser::ast::term::{Term, term};

    pub fn parse_term(interner: &mut Interner, source: &str) -> ParseResult<Term> {
        let context = ParseContext {
            interner,
            indent_levels: 0,
        };

        let (rest, term) = term()
            .parse(source, context)
            .expect("Term should have parsed");
        assert!(rest.is_empty(), "Leftover text when parsing term");

        term
    }
}
