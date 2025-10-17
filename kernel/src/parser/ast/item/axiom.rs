use crate::parser::ast::item::{LevelParameters, level_params};
use crate::parser::ast::term::{Binder, Term, bracketed_binder, term};
use crate::parser::atoms::ident::{OwnedPath, keyword, path};
use crate::parser::atoms::special_operator;
use crate::parser::atoms::whitespace::InBlockExt;
use crate::parser::combinators::repeat::Repeat0Ext;
use crate::parser::combinators::tuples::HeterogeneousTupleExt;
use crate::parser::{Parser, PrettyPrintContext};
use std::io::Write;
use common::PrettyPrint;

#[cfg_attr(any(test, debug_assertions), derive(PartialEq, Eq))]
#[derive(Debug)]
pub struct AxiomDefinition {
    pub path: OwnedPath,
    pub level_params: LevelParameters,
    pub binders: Vec<Binder>,
    pub ty: Term,
}

pub(super) fn axiom_definition() -> impl Parser<Output = AxiomDefinition> {
    rec!(
        (
            keyword("axiom"),
            (
                path(),
                level_params(),
                bracketed_binder().repeat_0(),
                special_operator(":"),
                term()
            )
                .sequence_with_whitespace()
                .in_block(),
        )
            .combine(|(_, (path, level_params, binders, _, ty))| {
                AxiomDefinition {
                    path,
                    level_params,
                    binders,
                    ty,
                }
            })
    )
}

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for AxiomDefinition {
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
        writeln!(out)?;
        writeln!(out)
    }
}
