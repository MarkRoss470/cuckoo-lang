pub mod data;
pub mod def;

use crate::parser::ast::item::data::{DataDefinition, data_definition};
use crate::parser::ast::item::def::{ValueDefinition, value_definition};
use crate::parser::ast::term::LevelExpr;
use crate::parser::atoms::ident::{Identifier, identifier};
use crate::parser::atoms::whitespace::SurroundWhitespaceExt;
use crate::parser::atoms::{special_operator, str_exact};
use crate::parser::combinators::modifiers::{IgnoreValExt, MapExt, OptionalExt};
use crate::parser::combinators::repeat::FinalSeparatorBehaviour::AllowFinal;
use crate::parser::combinators::repeat::Repeat1WithSeparatorExt;
use crate::parser::combinators::tuples::{HeterogeneousTupleExt, HomogeneousTupleExt};
use crate::parser::{Interner, Parser, PrettyPrint, PrettyPrintContext};
use crate::typeck::TypeError;
use std::io::Write;

#[derive(Debug)]
pub enum Item {
    DataDefinition(DataDefinition),
    Class,
    Instance,
    ValueDefinition(ValueDefinition),
}

pub(super) fn item() -> impl Parser<Output = Item> {
    (
        data_definition().map(Item::DataDefinition),
        value_definition().map(Item::ValueDefinition),
    )
        .alt()
}

#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug, Clone, Default)]
pub struct LevelParameters(pub Vec<Identifier>);

impl LevelParameters {
    pub fn new(params: &[Identifier]) -> Self {
        Self(params.to_vec())
    }

    /// Gets the number of level parameters
    pub fn count(&self) -> usize {
        self.0.len()
    }

    pub fn lookup(&self, arg: &Identifier) -> Option<usize> {
        self.0
            .iter()
            .enumerate()
            .find(|(_, id)| **id == *arg)
            .map(|(i, _)| i)
    }

    pub fn find_duplicate(&self) -> Option<Identifier> {
        for (i, u) in self.0.iter().enumerate() {
            if self.0[i + 1..].contains(u) {
                return Some(*u);
            }
        }

        None
    }
}

fn level_params() -> impl Parser<Output = LevelParameters> {
    rec!(
        (
            special_operator("."),
            str_exact("{"),
            identifier().repeat_1_with_separator(AllowFinal, str_exact(",").surround_whitespace()),
            str_exact("}"),
        )
            .combine_with_whitespace(|(_, _, ids, _)| LevelParameters(ids))
            .optional_or_default()
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
            _ => todo!(),
        }
    }
}

impl<'a> PrettyPrint<&'a Interner> for LevelParameters {
    fn pretty_print(&self, out: &mut dyn Write, context: &'a Interner) -> std::io::Result<()> {
        // Only print the braces if there's at least one parameter
        if !self.0.is_empty() {
            write!(out, ".{{")?;

            for param in &self.0 {
                param.pretty_print(out, context)?;
                write!(out, ", ")?;
            }

            write!(out, "}}")?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::tests::{ParseAllExt, setup_context};

    #[test]
    fn test_level_params() {
        setup_context!(context);

        let id_u = Identifier::from_str("u", context.interner);
        let id_v = Identifier::from_str("v", context.interner);
        let id_w = Identifier::from_str("w", context.interner);

        assert_eq!(
            level_params().parse_all(".{u}", context.borrow()),
            LevelParameters(vec![id_u])
        );

        assert_eq!(
            level_params().parse_all(".{ u , v,w,}", context.borrow()),
            LevelParameters(vec![id_u, id_v, id_w])
        );
    }
}
