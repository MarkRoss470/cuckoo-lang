use crate::parser::ast::term::{Term, term, Binder, bracketed_binder};
use crate::parser::atoms::whitespace::{InBlockExt, whitespace};
use crate::parser::atoms::{Identifier, identifier, keyword, special_operator, OwnedPath, path};
use crate::parser::combinators::repeat::Repeat0Ext;
use crate::parser::combinators::sequence::{CombineExt, SequenceExt};
use crate::parser::{Parser, PrettyPrint, PrettyPrintContext};
use std::io::Write;

#[derive(Debug)]
pub struct ValueDefinition {
    pub path: OwnedPath,
    pub binders: Vec<Binder>,
    pub ty: Term,
    pub value: Term,
}

pub fn value_definition() -> impl Parser<ValueDefinition> {
    (
        keyword("def"),
        whitespace(),
        (
            path(),
            whitespace(),
            bracketed_binder().repeat_0(),
            whitespace(),
            special_operator(":"),
            whitespace(),
            term(),
            whitespace(),
            special_operator(":="),
            whitespace(),
            term(),
        )
            .sequence()
            .in_block(),
    )
        .combine(
            |(_, _, (path, _, binders, _, _, _, ty, _, _, _, value))| ValueDefinition {
                path,
                binders,
                ty,
                value,
            },
        )
}

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for ValueDefinition {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext<'a>,
    ) -> std::io::Result<()> {
        write!(out, "def ")?;
        self.path.pretty_print(out, context.interner)?;
        write!(out, " : ")?;
        self.ty.pretty_print(out, context.borrow_indented())?;
        write!(out, " := ")?;
        self.value.pretty_print(out, context.borrow_indented())?;
        writeln!(out)?;
        writeln!(out)
    }
}
