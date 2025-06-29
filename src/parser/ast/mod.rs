use crate::parser::PrettyPrint;
use crate::parser::atoms::whitespace::whitespace;
use crate::parser::combinators::repeat::Repeat0Ext;
use crate::parser::combinators::sequence::CombineExt;
use crate::parser::{Interner, ParseContext, ParseResult};
use crate::parser::{Parser, PrettyPrintContext};
use item::{Item, item};

pub mod item;
pub mod term;

#[derive(Debug)]
pub struct Ast {
    pub interner: Interner,
    pub items: Vec<Item>,
}

pub fn parse_file(content: &str) -> ParseResult<Ast> {
    let mut interner = Interner::new();
    let context = ParseContext {
        interner: &mut interner,
        indent_levels: 0,
    };

    let (rest, res) = (whitespace(), item(), whitespace())
        .combine(|(_, i, _)| i)
        .repeat_0()
        .parse(content, context)
        .unwrap();

    if !rest.is_empty() {
        eprintln!("Some content unparsed:");
        eprintln!("{rest:?}");
    }

    res.map(|items| Ast { interner, items })
}

impl Ast {
    pub fn pretty_print(&self) {
        let context = PrettyPrintContext {
            interner: &self.interner,
            indent_levels: 0,
        };

        let mut stdout = std::io::stdout().lock();

        for item in &self.items {
            item.pretty_print(&mut stdout, context).unwrap();
        }
    }
    
    pub fn pretty_print_val<T: for<'a> PrettyPrint<PrettyPrintContext<'a>>>(&self, val: T) {
        let context = PrettyPrintContext {
            interner: &self.interner,
            indent_levels: 0,
        };

        let mut stdout = std::io::stdout().lock();

        val.pretty_print(&mut stdout, context).unwrap()
    }
}
