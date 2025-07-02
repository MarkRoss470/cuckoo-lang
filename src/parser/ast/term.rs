use crate::parser::atoms::whitespace::whitespace;
use crate::parser::atoms::{Identifier, identifier, keyword, special_operator, str_exact};
use crate::parser::combinators::alt::AltExt;
use crate::parser::combinators::modifiers::{DebugExt, InBoxExt, MapExt};
use crate::parser::combinators::repeat::{Fold1Ext, Repeat1Ext};
use crate::parser::combinators::sequence::CombineExt;
use crate::parser::{Interner, Parser, PrettyPrint, PrettyPrintContext, todo};
use std::io::Write;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Universe(usize);

impl Universe {
    pub const PROP: Self = Universe(0);
    pub const TYPE: Self = Universe(1);

    pub fn succ(self) -> Self {
        Self(self.0 + 1)
    }

    pub fn pred(self) -> Self {
        Self(self.0.saturating_sub(1))
    }

    pub fn max(self, other: Self) -> Self {
        Self(self.0.max(other.0))
    }
}

#[derive(Debug, Clone)]
pub enum Term {
    /// The keywords `Prop` or `Type n`
    SortLiteral(Universe),
    /// An identifier
    Identifier(Identifier),
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

#[derive(Debug, Clone)]
pub struct Binder {
    pub name: Option<Identifier>,
    pub ty: Term,
}

pub fn term() -> impl Parser<Term> {
    lambda_precedence_term()
}

fn lambda_precedence_term() -> impl Parser<Term> {
    rec!(
        (
            (
                keyword("fun"),
                whitespace(),
                bracketed_binder().repeat_1(),
                whitespace(),
                special_operator("=>"),
                whitespace(),
                lambda_precedence_term(),
            )
                .combine(|(_, _, binders, _, _, _, body)| binders.into_iter().rfold(
                    body,
                    |body, binder| Term::Lambda {
                        binder: Box::new(binder),
                        body: Box::new(body)
                    }
                )),
            pi_precedence_term(),
        )
            .alt()
    )
}

/// Parses a term with the precedence of a pi type or higher
fn pi_precedence_term() -> impl Parser<Term> {
    (pi_term(), application_precedence_term()).alt()
}

/// Parses a pi type term
fn pi_term() -> impl Parser<Term> {
    rec!(
        (
            binder().in_box(),
            whitespace(),
            special_operator("->"),
            whitespace(),
            pi_precedence_term().in_box(),
        )
            .combine(|(binder, _, _, _, output)| Term::PiType { binder, output })
    )
}

pub fn bracketed_binder() -> impl Parser<Binder> {
    (
        whitespace(),
        str_exact("("),
        whitespace(),
        identifier(),
        whitespace(),
        special_operator(":"),
        whitespace(),
        term(),
        whitespace(),
        str_exact(")"),
    )
        .combine(|(_, _, _, name, _, _, _, ty, _, _)| Binder {
            name: Some(name),
            ty,
        })
}

pub fn binder() -> impl Parser<Binder> {
    rec!(
        (
            bracketed_binder(),
            application_precedence_term().map(|ty| Binder { name: None, ty }),
        )
            .alt()
    )
}

fn application_precedence_term() -> impl Parser<Term> {
    atomic_term().fold_1(|l, r| Term::Application {
        function: Box::new(l),
        argument: Box::new(r),
    })
}

fn atomic_term() -> impl Parser<Term> {
    rec!(
        (
            (whitespace(), keyword("Type"), whitespace())
                .combine(|_| Term::SortLiteral(Universe::TYPE)),
            (whitespace(), keyword("Prop"), whitespace())
                .combine(|_| Term::SortLiteral(Universe::PROP)),
            (
                whitespace(),
                identifier().map(Term::Identifier),
                whitespace(),
            )
                .combine(|(_, t, _)| t),
            (
                whitespace(),
                str_exact("("),
                whitespace(),
                term(),
                whitespace(),
                str_exact(")"),
                whitespace(),
            )
                .combine(|(_, _, _, t, _, _, _)| t),
        )
            .alt()
    )
}

impl PrettyPrint<()> for Universe {
    fn pretty_print(&self, out: &mut dyn Write, _: ()) -> std::io::Result<()> {
        match self.0 {
            0 => write!(out, "Prop"),
            1 => write!(out, "Type"),
            n => write!(out, "(Type {})", n - 1),
        }
    }
}

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for Term {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext,
    ) -> std::io::Result<()> {
        match self {
            Term::SortLiteral(u) => u.pretty_print(out, ()),
            Term::Identifier(id) => id.pretty_print(out, context.interner),
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
