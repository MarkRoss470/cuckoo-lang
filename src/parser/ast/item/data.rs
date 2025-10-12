use crate::parser::ast::item::{LevelParameters, level_params};
use crate::parser::ast::term::{Binder, Term, bracketed_binder, term};
use crate::parser::atoms::ident::{Identifier, OwnedPath, identifier, keyword, path};
use crate::parser::atoms::special_operator;
use crate::parser::atoms::whitespace::InBlockExt;
use crate::parser::combinators::repeat::Repeat0Ext;
use crate::parser::combinators::tuples::HeterogeneousTupleExt;
use crate::parser::{Parser, PrettyPrint, PrettyPrintContext};
use std::io::Write;

#[cfg_attr(any(test, debug_assertions), derive(PartialEq, Eq))]
#[derive(Debug)]
pub struct DataDefinition {
    pub name: OwnedPath,
    pub level_params: LevelParameters,
    pub parameters: Vec<Binder>,
    pub family: Term,
    pub constructors: Vec<DataConstructor>,
}

#[cfg_attr(any(test, debug_assertions), derive(PartialEq, Eq))]
#[derive(Debug)]
pub struct DataConstructor {
    pub name: Identifier,
    pub telescope: Term,
}

pub(super) fn data_definition() -> impl Parser<Output = DataDefinition> {
    rec!(
        (
            keyword("data"),
            path(),
            level_params(),
            bracketed_binder().repeat_0(),
            special_operator(":"),
            term(),
            keyword("where"),
            data_constructor().repeat_0().in_block(),
        )
            .combine_with_whitespace(
                |(_, name, level_params, parameters, _, family, _, constructors)| {
                    DataDefinition {
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
            term().in_block(),
        )
            .combine_with_whitespace(|(_, name, _, telescope)| DataConstructor { name, telescope })
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
    use crate::parser::ast::term::{LevelArgs, LevelExpr};
    use crate::parser::atoms::ident::OwnedPath;
    use crate::parser::tests::{ParseAllExt, setup_context};

    #[test]
    fn test_data_definition() {
        setup_context!(context);

        let id_false = Identifier::from_str("False", context.interner);
        let data_false = data_definition().parse_all("data False : Prop where\n", context.borrow());

        assert_eq!(
            data_false,
            DataDefinition {
                name: OwnedPath::from_id(id_false),
                level_params: LevelParameters::default(),
                parameters: vec![],
                family: Term::Sort(Box::new(LevelExpr::PROP)),
                constructors: vec![],
            }
        );

        let id_nat = Identifier::from_str("Nat", context.interner);
        let id_zero = Identifier::from_str("zero", context.interner);
        let id_succ = Identifier::from_str("succ", context.interner);
        let data_nat = data_definition().parse_all(
            "data Nat : Type where\n  | zero : Nat\n  | succ : Nat -> Nat",
            context.borrow(),
        );

        assert_eq!(
            data_nat,
            DataDefinition {
                name: OwnedPath::from_id(id_nat),
                level_params: LevelParameters::default(),
                parameters: vec![],
                family: Term::Sort(Box::new(LevelExpr::TYPE)),
                constructors: vec![
                    DataConstructor {
                        name: id_zero,
                        telescope: Term::Path(OwnedPath::from_id(id_nat), LevelArgs::default())
                    },
                    DataConstructor {
                        name: id_succ,
                        telescope: Term::PiType {
                            binder: Box::new(Binder {
                                name: None,
                                ty: Term::Path(OwnedPath::from_id(id_nat), LevelArgs::default())
                            }),
                            output: Box::new(Term::Path(
                                OwnedPath::from_id(id_nat),
                                LevelArgs::default()
                            ))
                        }
                    }
                ],
            }
        );
    }
}
