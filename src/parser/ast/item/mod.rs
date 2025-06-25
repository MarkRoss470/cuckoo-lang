pub mod data;

use crate::parser::ast::item::data::{DataDefinition, data_definition};
use crate::parser::combinators::alt::AltExt;
use crate::parser::combinators::modifiers::MapExt;
use crate::parser::{Parser, PrettyPrint, PrettyPrintContext};
use std::io::Write;

#[derive(Debug)]
pub enum Item {
    DataDefinition(DataDefinition),
    Class,
    Instance,
    Def,
}

pub(super) fn item() -> impl Parser<Item> {
    (data_definition().map(Item::DataDefinition),).alt()
}

impl PrettyPrint for Item {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext,
    ) -> std::io::Result<()> {
        match self {
            Item::DataDefinition(d) => d.pretty_print(out, context),
            _ => todo!(),
        }
    }
}
