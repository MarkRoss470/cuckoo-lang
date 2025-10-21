use crate::ast::item::{LevelParameters, level_params};
use crate::ast::term::{Binder, Term, bracketed_binder, term};
use crate::atoms::ident::{OwnedPath, identifier, keyword, path};
use crate::atoms::special_operator;
use crate::atoms::whitespace::InBlockExt;
use crate::combinators::modifiers::MapExt;
use crate::combinators::modifiers::WithSpanExt;
use crate::combinators::repeat::Repeat0Ext;
use crate::combinators::tuples::HeterogeneousTupleExt;
use crate::error::Span;
use crate::{Parser, PrettyPrintContext};
use common::{Identifier, PrettyPrint};
use std::io::Write;

#[derive(Debug)]
pub struct DataDefinition {
    pub span: Span,
    pub name: OwnedPath,
    pub level_params: LevelParameters,
    pub parameters: Vec<Binder>,
    pub family: Term,
    pub constructors: Vec<DataConstructor>,
}

#[derive(Debug)]
pub struct DataConstructor {
    pub span: Span,
    pub name: Identifier,
    pub telescope: Term,
}

pub(super) fn data_definition() -> impl Parser<Output = DataDefinition> {
    rec!(
        (
            keyword("data"),
            (
                path(),
                level_params(),
                bracketed_binder().repeat_0(),
                special_operator(":"),
                term(),
                keyword("where"),
                data_constructor().repeat_0()
            )
                .sequence_with_whitespace()
                .in_block(),
        )
            .sequence()
            .with_span()
            .map(
                |((_, (name, level_params, parameters, _, family, _, constructors)), span)| {
                    DataDefinition {
                        span,
                        name,
                        level_params,
                        parameters,
                        family,
                        constructors,
                    }
                }
            )
    )
}

fn data_constructor() -> impl Parser<Output = DataConstructor> {
    rec!(
        (
            special_operator("|"),
            identifier(),
            special_operator(":"),
            term(),
        )
            .sequence_with_whitespace()
            .with_span()
            .map(|((_, name, _, telescope), span)| DataConstructor {
                span,
                name,
                telescope
            })
    )
}

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for DataDefinition {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext,
    ) -> std::io::Result<()> {
        write!(out, "data ")?;
        self.name.pretty_print(out, context.interner)?;

        self.level_params.pretty_print(out, context.interner)?;

        write!(out, " : ")?;
        self.family.pretty_print(out, context)?;
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

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for DataConstructor {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext,
    ) -> std::io::Result<()> {
        self.name.pretty_print(out, context.interner)?;
        write!(out, " : ")?;
        self.telescope.pretty_print(out, context)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::term::{LevelArgs, LevelExprKind, TermKind};
    use crate::atoms::ident::OwnedPath;
    use crate::tests::ParserTestExt;
    use common::{Identifier, Interner};

    #[test]
    fn test_data_definition() {
        let mut interner = Interner::new();

        let id_false = Identifier::from_str("False", &mut interner);
        let data_false = data_definition().parse_all("data False : Prop where", &mut interner);

        assert_eq!(data_false.name, OwnedPath::from_id(id_false));
        assert!(data_false.level_params.ids.is_empty());
        assert!(data_false.parameters.is_empty());
        let TermKind::Sort(false_level) = data_false.family.kind else {
            panic!()
        };
        assert_eq!(false_level.kind, LevelExprKind::PROP);
        assert!(data_false.constructors.is_empty());

        let id_nat = Identifier::from_str("Nat", &mut interner);
        let id_zero = Identifier::from_str("zero", &mut interner);
        let id_succ = Identifier::from_str("succ", &mut interner);
        let data_nat = data_definition().parse_all(
            "data Nat : Type where\n  | zero : Nat\n  | succ : Nat -> Nat",
            &mut interner,
        );

        assert_eq!(data_nat.name, OwnedPath::from_id(id_nat));
        assert!(data_nat.level_params.ids.is_empty());
        assert!(data_nat.parameters.is_empty());
        let TermKind::Sort(nat_level) = data_nat.family.kind else {
            panic!()
        };
        assert_eq!(nat_level.kind, LevelExprKind::TYPE);

        let [constructor_zero, constructor_succ] = data_nat.constructors.as_slice() else {
            panic!("Wrong number of constructors")
        };

        assert_eq!(constructor_zero.name, id_zero);
        assert_eq!(
            constructor_zero.telescope.kind,
            TermKind::Path(OwnedPath::from_id(id_nat), LevelArgs::default())
        );

        assert_eq!(constructor_succ.name, id_succ);
        let TermKind::PiType { binder, output } = &constructor_succ.telescope.kind else {
            panic!("Succ constructor should have been a pi type")
        };

        assert_eq!(binder.names, vec![None]);
        assert_eq!(
            binder.ty.kind,
            TermKind::Path(OwnedPath::from_id(id_nat), LevelArgs::default())
        );
        assert_eq!(
            output.kind,
            TermKind::Path(OwnedPath::from_id(id_nat), LevelArgs::default())
        );
    }
}
