use crate::ast::item::{LevelParameters, level_params};
use crate::ast::term::{Binder, Term, bracketed_binder, term};
use crate::atoms::ident::{OwnedPath, keyword, path};
use crate::atoms::special_operator;
use crate::atoms::whitespace::InBlockExt;
use crate::combinators::modifiers::MapExt;
use crate::combinators::modifiers::WithSpanExt;
use crate::combinators::repeat::Repeat0Ext;
use crate::combinators::tuples::HeterogeneousTupleExt;
use crate::error::Span;
use crate::{Parser, PrettyPrintContext};
use common::PrettyPrint;
use std::io::Write;

#[derive(Debug)]
pub struct AxiomDefinition {
    pub span: Span,
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
            .sequence()
            .with_span()
            .map(|((_, (path, level_params, binders, _, ty)), span)| {
                AxiomDefinition {
                    span,
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
