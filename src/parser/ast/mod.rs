use std::any::type_name_of_val;
use crate::parser::PrettyPrint;
use crate::parser::combinators::repeat::Repeat0Ext;
use crate::parser::{Interner, ParseContext, ParseResult};
use crate::parser::{Parser, PrettyPrintContext};
use item::{Item, item};

pub mod item;
mod term;

#[derive(Debug)]
pub struct Ast {
    interner: Interner,
    items: Vec<Item>,
}

pub fn parse_file(content: &str) -> ParseResult<Ast> {
    let mut interner = Interner::new();
    let context = ParseContext {
        interner: &mut interner,
        indent_levels: 0,
    };

    println!("{}", type_name_of_val(&item().repeat_0()));
    
    let (rest, res) = item().repeat_0().parse(content, context).unwrap();

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
}
