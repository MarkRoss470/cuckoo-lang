pub mod data;
pub mod def;

use crate::parser::ast::item::data::{DataDefinition, data_definition};
use crate::parser::ast::item::def::{ValueDefinition, value_definition};
use crate::parser::combinators::alt::AltExt;
use crate::parser::combinators::modifiers::MapExt;
use crate::parser::{Parser, PrettyPrint, PrettyPrintContext};
use std::io::Write;

#[derive(Debug)]
pub enum Item {
    DataDefinition(DataDefinition),
    Class,
    Instance,
    ValueDefinition(ValueDefinition),
}

pub(super) fn item() -> impl Parser<Item> {
    (
        data_definition().map(Item::DataDefinition),
        value_definition().map(Item::ValueDefinition),
    )
        .alt()
}

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for Item {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext,
    ) -> std::io::Result<()> {
        match self {
            Item::DataDefinition(d) => d.pretty_print(out, context),
            Item::ValueDefinition(v) => v.pretty_print(out, context),
            _ => todo!(),
        }
    }
}
