use crate::parser::ast::term::{Term, term};
use crate::parser::atoms::whitespace::{InBlockExt, newline_and_indent, whitespace};
use crate::parser::atoms::{Identifier, identifier, keyword, str_exact};
use crate::parser::combinators::repeat::Repeat0Ext;
use crate::parser::combinators::sequence::CombineExt;
use crate::parser::{Parser, PrettyPrint, PrettyPrintContext};
use std::io::Write;

#[derive(Debug)]
pub struct DataDefinition {
    pub name: Identifier,
    pub constructors: Vec<DataConstructor>,
}

#[derive(Debug)]
pub struct DataConstructor {
    pub name: Identifier,
    pub telescope: Term,
}

pub(super) fn data_definition() -> impl Parser<DataDefinition> {
    rec!(
        (
            keyword("data"),
            whitespace(),
            identifier(),
            whitespace(),
            keyword("where"),
            data_constructor().repeat_0().in_block(),
        )
            .combine(|(_, _, name, _, _, constructors)| DataDefinition { name, constructors })
    )
}

fn data_constructor() -> impl Parser<DataConstructor> {
    rec!(
        (
            newline_and_indent(),
            whitespace(),
            identifier(),
            whitespace(),
            str_exact(":"), // TODO: replace with some operator type thing
            term().in_block(),
        )
            .combine(|(_, _, name, _, _, telescope)| DataConstructor { name, telescope })
    )
}

impl PrettyPrint for DataDefinition {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext,
    ) -> std::io::Result<()> {
        write!(out, "data ")?;
        self.name.pretty_print(out, context)?;
        write!(out, " where")?;

        {
            let context = context.borrow_indented();

            for constructor in &self.constructors {
                context.newline(out)?;
                constructor.pretty_print(out, context)?;
            }
        }

        context.newline(out)?;
        context.newline(out)
    }
}

impl PrettyPrint for DataConstructor {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext,
    ) -> std::io::Result<()> {
        self.name.pretty_print(out, context)?;
        write!(out, " : ")?;
        self.telescope.pretty_print(out, context)
    }
}
