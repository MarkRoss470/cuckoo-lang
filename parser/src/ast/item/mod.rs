pub mod axiom;
pub mod data;
pub mod def;
pub mod import;

use crate::ast::item::axiom::{AxiomDefinition, axiom_definition};
use crate::ast::item::data::{DataDefinition, data_definition};
use crate::ast::item::def::{ValueDefinition, value_definition};
use crate::atoms::ident::identifier;
use crate::atoms::whitespace::{InBlockExt, SurroundWhitespaceExt, newlines_and_indent};
use crate::atoms::{char, span, special_operator, str_exact};
use crate::combinators::error::OrErrorExt;
use crate::combinators::modifiers::{IgnoreValExt, MapExt, MapStrExt, VerifyExt, WithSpanExt};
use crate::combinators::repeat::FinalSeparatorBehaviour::AllowFinal;
use crate::combinators::repeat::{Repeat0Ext, Repeat1Ext, Repeat1WithSeparatorExt};
use crate::combinators::tuples::{HeterogeneousTupleExt, HomogeneousTupleExt};
use crate::error::{ParseDiagnosticKind, Span};
use crate::{Parser, PrettyPrintContext};
use common::{Identifier, Interner, PrettyPrint};
use std::io::Write;

#[derive(Debug)]
pub enum Item {
    DataDefinition(DataDefinition),
    ValueDefinition(ValueDefinition),
    Axiom(AxiomDefinition),
    Malformed(Span),
}

pub(super) fn item() -> impl Parser<Output = Item> {
    rec!(
        (
            data_definition().map(Item::DataDefinition),
            value_definition().map(Item::ValueDefinition),
            axiom_definition().map(Item::Axiom),
        )
            .alt()
            .or_else_error(|| ParseDiagnosticKind::MalformedItem, malformed_item())
    )
}

fn malformed_item() -> impl Parser<Output = Item> {
    rec!(
        (
            char().verify(|c| *c != '\n').ignore_value(),
            newlines_and_indent(),
        )
            .alt()
            .repeat_0()
            .in_block()
            .with_span()
            .map(|(_, span)| Item::Malformed(span))
    )
}

#[cfg_attr(any(test, feature = "test-utils"), derive(PartialEq, Eq))]
#[derive(Debug, Clone)]
pub struct LevelParameters {
    pub span: Span,
    pub ids: Vec<Identifier>,
}

impl LevelParameters {
    /// Gets the number of level parameters
    pub fn count(&self) -> usize {
        self.ids.len()
    }

    pub fn lookup(&self, arg: &Identifier) -> Option<usize> {
        self.ids
            .iter()
            .enumerate()
            .find(|(_, id)| **id == *arg)
            .map(|(i, _)| i)
    }

    pub fn find_duplicate(&self) -> Option<Identifier> {
        for (i, u) in self.ids.iter().enumerate() {
            if self.ids[i + 1..].contains(u) {
                return Some(*u);
            }
        }

        None
    }

    /// Finds an identifier based on the given string which is not contained in `self`
    pub fn unused_ident_from(&self, id: &str, interner: &mut Interner) -> Identifier {
        let raw = Identifier::from_str(id, interner);

        if self.lookup(&raw).is_none() {
            return raw;
        }

        for x in 1usize.. {
            let with_tag = Identifier::from_str(&format!("{id}_{x}"), interner);

            if self.lookup(&with_tag).is_none() {
                return with_tag;
            }
        }

        unreachable!()
    }
}

fn level_params() -> impl Parser<Output = LevelParameters> {
    rec!(
        (
            (
                special_operator("."),
                str_exact("{"),
                identifier()
                    .repeat_1_with_separator(AllowFinal, str_exact(",").surround_whitespace()),
                str_exact("}"),
            )
                .sequence_with_whitespace()
                .with_span()
                .map(|((_, _, ids, _), span)| LevelParameters { span, ids }),
            span().map(|span| LevelParameters { span, ids: vec![] })
        )
            .alt()
    )
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
            Item::Axiom(a) => a.pretty_print(out, context),
            Item::Malformed(s) => write!(out, "Malformed item at {s}"),
        }
    }
}

impl<'a> PrettyPrint<&'a Interner> for LevelParameters {
    fn pretty_print(&self, out: &mut dyn Write, context: &'a Interner) -> std::io::Result<()> {
        // Only print the braces if there's at least one parameter
        if !self.ids.is_empty() {
            write!(out, ".{{")?;

            for param in &self.ids {
                param.pretty_print(out, context)?;
                write!(out, ", ")?;
            }

            write!(out, "}}")?;
        }

        Ok(())
    }
}

#[cfg(any(test, feature = "test-utils"))]
impl LevelParameters {
    pub fn new(params: &[Identifier]) -> Self {
        Self {
            span: Span::dummy(),
            ids: params.to_vec(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::ParserTestExt;
    use common::Identifier;

    #[test]
    fn test_level_params() {
        let mut interner = Interner::new();

        let id_u = Identifier::from_str("u", &mut interner);
        let id_v = Identifier::from_str("v", &mut interner);
        let id_w = Identifier::from_str("w", &mut interner);

        assert_eq!(
            level_params().parse_all(".{u}", &mut interner),
            LevelParameters::new(&[id_u])
        );

        assert_eq!(
            level_params().parse_all(".{ u , v,w,}", &mut interner),
            LevelParameters::new(&[id_u, id_v, id_w])
        );
    }
}
