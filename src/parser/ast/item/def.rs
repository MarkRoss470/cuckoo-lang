use crate::parser::ast::item::{LevelParameters, level_params};
use crate::parser::ast::term::{Binder, Term, bracketed_binder, term};
use crate::parser::atoms::whitespace::{InBlockExt, whitespace};
use crate::parser::combinators::modifiers::OptionalExt;
use crate::parser::combinators::repeat::Repeat0Ext;
use crate::parser::combinators::tuples::HeterogeneousTupleExt;
use crate::parser::{Parser, PrettyPrint, PrettyPrintContext};
use std::io::Write;
use crate::parser::atoms::ident::{keyword, path, OwnedPath};
use crate::parser::atoms::special_operator;

#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug)]
pub struct ValueDefinition {
    pub path: OwnedPath,
    pub level_params: LevelParameters,
    pub binders: Vec<Binder>,
    pub ty: Term,
    pub value: Term,
}

pub fn value_definition() -> impl Parser<Output = ValueDefinition> {
    rec!(
        (
            keyword("def"),
            path(),
            level_params(),
            bracketed_binder().repeat_0(),
            special_operator(":"),
            term(),
            special_operator(":="),
            term().in_block(),
        )
            .combine_with_whitespace(|(_, path, level_params, binders, _, ty, _, value)| {
                ValueDefinition {
                    path,
                    level_params,
                    binders,
                    ty,
                    value,
                }
            })
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

        self.level_params.pretty_print(out, context.interner)?;

        write!(out, " : ")?;
        self.ty.pretty_print(out, context.borrow_indented())?;
        write!(out, " := ")?;
        self.value.pretty_print(out, context.borrow_indented())?;
        writeln!(out)?;
        writeln!(out)
    }
}
