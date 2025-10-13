use crate::parser::atoms::ident::{Identifier, OwnedPath, identifier, keyword, path};
use crate::parser::atoms::literal::nat_literal;
use crate::parser::atoms::whitespace::{SurroundWhitespaceExt, whitespace};
use crate::parser::atoms::{special_operator, str_exact};
use crate::parser::combinators::modifiers::IgnoreValExt;
use crate::parser::combinators::modifiers::InBoxExt;
use crate::parser::combinators::modifiers::MapExt;
use crate::parser::combinators::modifiers::OptionalExt;
use crate::parser::combinators::repeat::FinalSeparatorBehaviour::AllowFinal;
use crate::parser::combinators::repeat::{Fold1Ext, Repeat1Ext, Repeat1WithSeparatorExt};
use crate::parser::combinators::tuples::{HeterogeneousTupleExt, HomogeneousTupleExt};
use crate::parser::{Interner, Parser, PrettyPrint, PrettyPrintContext};
use std::io::Write;

#[cfg_attr(any(test, debug_assertions), derive(PartialEq, Eq))]
#[derive(Debug, Clone)]
pub enum LevelExpr {
    Literal(usize),
    Parameter(Identifier),
    Succ(Box<LevelExpr>),
    Max(Box<LevelExpr>, Box<LevelExpr>),
    IMax(Box<LevelExpr>, Box<LevelExpr>),
}

impl LevelExpr {
    pub const PROP: Self = LevelExpr::Literal(0);
    pub const TYPE: Self = LevelExpr::Literal(1);
}

#[cfg_attr(any(test, debug_assertions), derive(PartialEq, Eq))]
#[derive(Debug, Clone, Default)]
pub struct LevelArgs(Vec<LevelExpr>);

impl LevelArgs {
    pub fn iter(&self) -> impl Iterator<Item = &LevelExpr> {
        self.0.iter()
    }
}

#[cfg_attr(any(test, debug_assertions), derive(PartialEq, Eq))]
#[derive(Debug, Clone)]
pub enum Term {
    /// The keywords `Prop` or `Type n`
    Sort(Box<LevelExpr>),
    /// A path
    Path(OwnedPath, LevelArgs),
    /// A function application
    Application {
        function: Box<Term>,
        argument: Box<Term>,
    },
    /// A function / pi type
    PiType {
        binder: Box<Binder>,
        output: Box<Term>,
    },
    /// A lambda abstraction
    Lambda {
        binder: Box<Binder>,
        body: Box<Term>,
    },
}

#[cfg_attr(any(test, debug_assertions), derive(PartialEq, Eq))]
#[derive(Debug, Clone)]
pub struct Binder {
    pub name: Option<Identifier>,
    pub ty: Term,
}

pub(in crate::parser) fn term() -> impl Parser<Output = Term> {
    lambda_precedence_term()
}

fn lambda_precedence_term() -> impl Parser<Output = Term> {
    rec!(
        (
            (
                keyword("fun"),
                bracketed_binder().repeat_1(),
                special_operator("=>"),
                lambda_precedence_term(),
            )
                .combine_with_whitespace(|(_, binders, _, body)| binders
                    .into_iter()
                    .rfold(body, |body, binder| Term::Lambda {
                        binder: Box::new(binder),
                        body: Box::new(body)
                    })),
            pi_precedence_term(),
        )
            .alt()
    )
}

/// Parses a term with the precedence of a pi type or higher
fn pi_precedence_term() -> impl Parser<Output = Term> {
    (pi_term(), application_precedence_term()).alt()
}

/// Parses a pi type term
fn pi_term() -> impl Parser<Output = Term> {
    rec!(
        (
            binder().in_box(),
            special_operator("->"),
            pi_precedence_term().in_box(),
        )
            .combine_with_whitespace(|(binder, _, output)| Term::PiType { binder, output })
    )
}

pub(in crate::parser) fn bracketed_binder() -> impl Parser<Output = Binder> {
    rec!(
        (
            str_exact("("),
            (
                identifier().map(Some),
                keyword("_").with_value(None)
            )
                .alt(),
            special_operator(":"),
            term(),
            str_exact(")"),
        )
            .combine_with_whitespace(|(_, name, _, ty, _)| Binder { name, ty })
    )
}

pub(in crate::parser) fn binder() -> impl Parser<Output = Binder> {
    rec!(
        (
            bracketed_binder(),
            application_precedence_term().map(|ty| Binder { name: None, ty }),
        )
            .alt()
    )
}

fn application_precedence_term() -> impl Parser<Output = Term> {
    sort_precedence_term().then_fold(atomic_term(), |l, r| Term::Application {
        function: Box::new(l),
        argument: Box::new(r),
    })
}

fn sort_precedence_term() -> impl Parser<Output = Term> {
    (
        (keyword("Sort"), level_expr()).combine_with_whitespace(|(_, u)| Term::Sort(Box::new(u))),
        (keyword("Type"), level_expr())
            .combine_with_whitespace(|(_, u)| Term::Sort(Box::new(LevelExpr::Succ(Box::new(u))))),
        atomic_term(),
    )
        .alt()
}

fn atomic_term() -> impl Parser<Output = Term> {
    rec!(
        (
            keyword("Sort")
                .surround_whitespace()
                .with_value(Term::Sort(Box::new(LevelExpr::PROP))),
            keyword("Type")
                .surround_whitespace()
                .with_value(Term::Sort(Box::new(LevelExpr::TYPE))),
            keyword("Prop")
                .surround_whitespace()
                .with_value(Term::Sort(Box::new(LevelExpr::PROP))),
            path_term(),
            (str_exact("("), term(), str_exact(")"),).combine_with_whitespace(|(_, t, _)| t),
        )
            .alt()
    )
}

fn path_term() -> impl Parser<Output = Term> {
    (whitespace(), path(), level_args())
        .combine(|(_, path, level_args)| Term::Path(path, level_args))
}

fn level_args() -> impl Parser<Output = LevelArgs> {
    (
        str_exact(".{"),
        level_expr().repeat_1_with_separator(AllowFinal, str_exact(",").surround_whitespace()),
        str_exact("}"),
    )
        .combine(|(_, args, _)| LevelArgs(args))
        .optional_or_default()
}

fn level_expr() -> impl Parser<Output = LevelExpr> {
    rec!(
        (
            nat_literal().map(LevelExpr::Literal).surround_whitespace(),
            identifier().map(LevelExpr::Parameter).surround_whitespace(),
            (
                str_exact("("),
                keyword("succ"),
                level_expr(),
                str_exact(")")
            )
                .combine_with_whitespace(|(_, _, u, _)| LevelExpr::Succ(Box::new(u))),
            (
                str_exact("("),
                keyword("max"),
                level_expr(),
                level_expr(),
                str_exact(")")
            )
                .combine_with_whitespace(|(_, _, u, v, _)| LevelExpr::Max(
                    Box::new(u),
                    Box::new(v)
                )),
            (
                str_exact("("),
                keyword("imax"),
                level_expr(),
                level_expr(),
                str_exact(")")
            )
                .combine_with_whitespace(|(_, _, u, v, _)| LevelExpr::IMax(
                    Box::new(u),
                    Box::new(v)
                )),
            (str_exact("("), level_expr(), str_exact(")")).combine_with_whitespace(|(_, u, _)| u)
        )
            .alt()
    )
}

impl<'a> PrettyPrint<&'a Interner> for LevelExpr {
    fn pretty_print(&self, out: &mut dyn Write, context: &'a Interner) -> std::io::Result<()> {
        match self {
            LevelExpr::Literal(u) => write!(out, "{u}"),
            LevelExpr::Parameter(v) => v.pretty_print(out, context),
            LevelExpr::Succ(u) => {
                write!(out, "(succ ")?;
                u.pretty_print(out, context)?;
                write!(out, ")")
            }
            LevelExpr::Max(u, v) => {
                write!(out, "(max ")?;
                u.pretty_print(out, context)?;
                write!(out, ", ")?;
                v.pretty_print(out, context)?;
                write!(out, ")")
            }
            LevelExpr::IMax(u, v) => {
                write!(out, "(imax ")?;
                u.pretty_print(out, context)?;
                write!(out, ", ")?;
                v.pretty_print(out, context)?;
                write!(out, ")")
            }
        }
    }
}

impl<'a> PrettyPrint<&'a Interner> for LevelArgs {
    fn pretty_print(&self, out: &mut dyn Write, context: &'a Interner) -> std::io::Result<()> {
        if self.0.len() == 0 {
            return Ok(());
        }

        write!(out, ".{{")?;
        for arg in &self.0 {
            arg.pretty_print(out, context)?;
        }
        write!(out, "}}")
    }
}

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for Term {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext,
    ) -> std::io::Result<()> {
        match self {
            Term::Sort(u) => {
                write!(out, "Sort ")?;
                u.pretty_print(out, context.interner)
            }
            Term::Path(id, level_args) => {
                id.pretty_print(out, context.interner)?;
                level_args.pretty_print(out, context.interner)
            }
            Term::Application { function, argument } => {
                write!(out, "(")?;
                function.pretty_print(out, context)?;
                write!(out, " ")?;
                argument.pretty_print(out, context)?;
                write!(out, ")")
            }
            Term::PiType { binder, output } => {
                write!(out, "(")?;
                binder.pretty_print(out, context)?;
                write!(out, " -> ")?;
                output.pretty_print(out, context)?;
                write!(out, ")")
            }
            Term::Lambda { binder, body } => {
                write!(out, "(fun ")?;
                binder.pretty_print(out, context)?;
                write!(out, " => ")?;
                body.pretty_print(out, context)?;
                write!(out, ")")
            }
        }
    }
}

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for Binder {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext<'_>,
    ) -> Result<(), std::io::Error> {
        write!(out, "(")?;
        match &self.name {
            None => write!(out, "_")?,
            Some(id) => id.pretty_print(out, context.interner)?,
        }
        write!(out, " : ")?;

        self.ty.pretty_print(out, context)?;
        write!(out, ")")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::tests::{ParseAllExt, setup_context};

    #[test]
    fn test_pi_type() {
        setup_context!(context);

        let id_u = Identifier::from_str("u", context.interner);

        assert_eq!(
            term().parse_all("u -> u", context),
            Term::PiType {
                binder: Box::new(Binder {
                    name: None,
                    ty: Term::Path(OwnedPath::from_id(id_u), LevelArgs::default())
                }),
                output: Box::new(Term::Path(OwnedPath::from_id(id_u), LevelArgs::default()))
            }
        )
    }
}
