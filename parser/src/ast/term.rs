use crate::atoms::ident::{OwnedPath, identifier, keyword, path};
use crate::atoms::literal::nat_literal;
use crate::atoms::whitespace::{SurroundWhitespaceExt, whitespace};
use crate::atoms::{just, span, special_operator, str_exact};
use crate::combinators::error::OrErrorExt;
use crate::combinators::modifiers::InBoxExt;
use crate::combinators::modifiers::MapExt;
use crate::combinators::modifiers::OptionalExt;
use crate::combinators::modifiers::{IgnoreValExt, WithSpanExt};
use crate::combinators::repeat::FinalSeparatorBehaviour::AllowFinal;
use crate::combinators::repeat::{Fold1Ext, Repeat1Ext, Repeat1WithSeparatorExt};
use crate::combinators::tuples::{HeterogeneousTupleExt, HomogeneousTupleExt};
use crate::error::{ParseDiagnosticKind, SourceLocation, Span};
use crate::{ParseResult, Parser, PrettyPrintContext, parser};
use common::{Identifier, Interner, PrettyPrint};
use std::io::Write;

#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug, Clone)]
pub struct LevelExpr {
    pub span: Span,
    pub kind: LevelExprKind,
}

#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug, Clone)]
pub enum LevelExprKind {
    Literal(usize),
    Parameter(Identifier),
    Succ(Box<LevelExpr>),
    Max(Box<LevelExpr>, Box<LevelExpr>),
    IMax(Box<LevelExpr>, Box<LevelExpr>),

    /// A hole left for inference to fill
    Underscore,
    /// A malformed level expression
    Malformed,
}

impl LevelExprKind {
    pub const PROP: Self = LevelExprKind::Literal(0);
    pub const TYPE: Self = LevelExprKind::Literal(1);
}

#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug, Clone, Default)]
pub struct LevelArgs(Vec<LevelExpr>);

impl LevelArgs {
    pub fn iter(&self) -> impl Iterator<Item = &LevelExpr> {
        self.0.iter()
    }
}

#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug, Clone)]
pub struct Term {
    pub span: Span,
    pub kind: TermKind,
}

#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug, Clone)]
pub enum TermKind {
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

    /// A hole left for inference to fill
    Underscore,
    /// A malformed term
    Malformed,
}

impl Term {
    fn malformed_at(span: Span) -> Self {
        Self {
            span,
            kind: TermKind::Malformed,
        }
    }

    fn underscore_at(span: Span) -> Self {
        Self {
            span,
            kind: TermKind::Underscore,
        }
    }
}

#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug, Clone)]
pub struct Binder {
    pub span: Span,
    pub names: Vec<Option<Identifier>>,
    pub ty: Term,
}

pub(crate) fn term() -> impl Parser<Output = Term> {
    lambda_precedence_term()
}

trait MapTermExt: Parser {
    fn map_term(self, f: impl Fn(Self::Output) -> TermKind) -> impl Parser<Output = Term>;
}

impl<P: Parser> MapTermExt for P {
    fn map_term(self, f: impl Fn(Self::Output) -> TermKind) -> impl Parser<Output = Term> {
        self.with_span()
            .map(move |(v, span)| Term { span, kind: f(v) })
    }
}

fn malformed_term() -> impl Parser<Output = Term> {
    parser(|input, context| {
        Some((
            input,
            ParseResult::new(Term::malformed_at(context.location_of(input))),
        ))
    })
}

fn lambda_precedence_term() -> impl Parser<Output = Term> {
    rec!(
        (
            (
                keyword("fun"),
                lambda_binders(),
                special_operator("=>").or_error(|| ParseDiagnosticKind::MissingLambdaArrow),
                lambda_precedence_term()
                    .or_else_error(|| ParseDiagnosticKind::MissingLambdaBody, malformed_term()),
            )
                .sequence_with_whitespace()
                .with_span()
                .map(|((_, binders, _, body), span)| binders.into_iter().rfold(
                    body,
                    |body, binder| Term {
                        span: span.clone(),
                        kind: TermKind::Lambda {
                            binder: Box::new(binder),
                            body: Box::new(body)
                        }
                    }
                )),
            pi_precedence_term(),
        )
            .alt()
    )
}

fn lambda_binders() -> impl Parser<Output = Vec<Binder>> {
    rec!(
        (
            bracketed_binder(),
            identifier().with_span().map(|(id, span)| Binder {
                span: span.clone(),
                names: vec![Some(id)],
                ty: Term {
                    span,
                    kind: TermKind::Underscore,
                },
            }),
        )
            .alt()
            .repeat_1()
            .or_else_error(
                || ParseDiagnosticKind::MissingLambdaBinder,
                span().map(|span| {
                    vec![Binder {
                        span: span.clone(),
                        names: vec![None],
                        ty: Term::underscore_at(span),
                    }]
                }),
            )
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
            .sequence_with_whitespace()
            .map_term(|(binder, _, output)| TermKind::PiType { binder, output })
    )
}

pub(crate) fn bracketed_binder() -> impl Parser<Output = Binder> {
    rec!(
        (
            str_exact("("),
            (identifier().map(Some), keyword("_").with_value(None))
                .alt()
                .surround_whitespace()
                .repeat_1()
                .or_else_error(|| ParseDiagnosticKind::MissingBinderName, just(vec![None])),
            special_operator(":"),
            term(),
            str_exact(")"),
        )
            .sequence_with_whitespace()
            .with_span()
            .map(|((_, names, _, ty, _), span)| Binder { span, names, ty })
    )
}

pub(crate) fn binder() -> impl Parser<Output = Binder> {
    rec!(
        (
            bracketed_binder(),
            application_precedence_term().map(|ty| Binder {
                span: ty.span.clone(),
                names: vec![None],
                ty
            }),
        )
            .alt()
    )
}

fn application_precedence_term() -> impl Parser<Output = Term> {
    rec!(
        sort_precedence_term().then_fold(atomic_term(), |l, r| Term {
            span: l.span.union(&r.span),
            kind: TermKind::Application {
                function: Box::new(l),
                argument: Box::new(r),
            },
        })
    )
}

fn sort_precedence_term() -> impl Parser<Output = Term> {
    rec!(
        (
            (keyword("Sort"), level_expr())
                .sequence_with_whitespace()
                .map_term(|(_, u)| TermKind::Sort(Box::new(u))),
            (keyword("Type"), level_expr())
                .sequence_with_whitespace()
                .with_span()
                .map_term(|((_, u), span)| {
                    TermKind::Sort(Box::new(LevelExpr {
                        span,
                        kind: LevelExprKind::Succ(Box::new(u)),
                    }))
                }),
            atomic_term(),
        )
            .alt()
    )
}

fn atomic_term() -> impl Parser<Output = Term> {
    rec!(
        (
            keyword("Sort")
                .with_span()
                .surround_whitespace()
                .map_term(|(_, span)| TermKind::Sort(Box::new(LevelExpr {
                    span,
                    kind: LevelExprKind::PROP
                }))),
            keyword("Type")
                .with_span()
                .surround_whitespace()
                .map_term(|(_, span)| TermKind::Sort(Box::new(LevelExpr {
                    span,
                    kind: LevelExprKind::TYPE
                }))),
            keyword("Prop")
                .with_span()
                .surround_whitespace()
                .map_term(|(_, span)| TermKind::Sort(Box::new(LevelExpr {
                    span,
                    kind: LevelExprKind::PROP
                }))),
            path_term(),
            keyword("_")
                .surround_whitespace()
                .map_term(|_| TermKind::Underscore),
            (str_exact("("), term(), str_exact(")"),).combine_with_whitespace(|(_, t, _)| t),
        )
            .alt()
    )
}

fn path_term() -> impl Parser<Output = Term> {
    rec!(
        (whitespace(), path(), level_args())
            .sequence()
            .map_term(|(_, path, level_args)| TermKind::Path(path, level_args))
    )
}

fn level_args() -> impl Parser<Output = LevelArgs> {
    rec!(
        (
            str_exact(".{"),
            level_expr().repeat_1_with_separator(AllowFinal, str_exact(",").surround_whitespace()),
            str_exact("}"),
        )
            .combine(|(_, args, _)| LevelArgs(args))
            .optional_or_default()
    )
}

fn level_expr() -> impl Parser<Output = LevelExpr> {
    rec!(
        (
            nat_literal()
                .map(LevelExprKind::Literal)
                .surround_whitespace(),
            identifier()
                .map(LevelExprKind::Parameter)
                .surround_whitespace(),
            (
                str_exact("("),
                keyword("succ"),
                level_expr(),
                str_exact(")")
            )
                .combine_with_whitespace(|(_, _, u, _)| LevelExprKind::Succ(Box::new(u))),
            (
                str_exact("("),
                keyword("max"),
                level_expr(),
                level_expr(),
                str_exact(")")
            )
                .combine_with_whitespace(|(_, _, u, v, _)| LevelExprKind::Max(
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
                .combine_with_whitespace(|(_, _, u, v, _)| LevelExprKind::IMax(
                    Box::new(u),
                    Box::new(v)
                )),
            keyword("_").with_value(LevelExprKind::Underscore),
            (str_exact("("), level_expr(), str_exact(")"))
                .combine_with_whitespace(|(_, u, _)| u.kind)
        )
            .alt()
            .with_span()
            .map(|(kind, span)| LevelExpr { span, kind })
    )
}

impl<'a> PrettyPrint<&'a Interner> for LevelExpr {
    fn pretty_print(&self, out: &mut dyn Write, context: &'a Interner) -> std::io::Result<()> {
        match &self.kind {
            LevelExprKind::Literal(u) => write!(out, "{u}"),
            LevelExprKind::Parameter(v) => v.pretty_print(out, context),
            LevelExprKind::Succ(u) => {
                write!(out, "(succ ")?;
                u.pretty_print(out, context)?;
                write!(out, ")")
            }
            LevelExprKind::Max(u, v) => {
                write!(out, "(max ")?;
                u.pretty_print(out, context)?;
                write!(out, ", ")?;
                v.pretty_print(out, context)?;
                write!(out, ")")
            }
            LevelExprKind::IMax(u, v) => {
                write!(out, "(imax ")?;
                u.pretty_print(out, context)?;
                write!(out, ", ")?;
                v.pretty_print(out, context)?;
                write!(out, ")")
            }
            LevelExprKind::Underscore => write!(out, "_"),
            LevelExprKind::Malformed => write!(out, "<malformed>"),
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
        context: PrettyPrintContext<'a>,
    ) -> std::io::Result<()> {
        self.kind.pretty_print(out, context)
    }
}

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for TermKind {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext,
    ) -> std::io::Result<()> {
        match self {
            TermKind::Sort(u) => {
                write!(out, "Sort ")?;
                u.pretty_print(out, context.interner)
            }
            TermKind::Path(id, level_args) => {
                id.pretty_print(out, context.interner)?;
                level_args.pretty_print(out, context.interner)
            }
            TermKind::Application { function, argument } => {
                write!(out, "(")?;
                function.pretty_print(out, context)?;
                write!(out, " ")?;
                argument.pretty_print(out, context)?;
                write!(out, ")")
            }
            TermKind::PiType { binder, output } => {
                write!(out, "(")?;
                binder.pretty_print(out, context)?;
                write!(out, " -> ")?;
                output.pretty_print(out, context)?;
                write!(out, ")")
            }
            TermKind::Lambda { binder, body } => {
                write!(out, "(fun ")?;
                binder.pretty_print(out, context)?;
                write!(out, " => ")?;
                body.pretty_print(out, context)?;
                write!(out, ")")
            }
            TermKind::Underscore => write!(out, "_"),
            TermKind::Malformed => write!(out, "<malformed>"),
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

        for name in &self.names {
            match name {
                None => write!(out, "_")?,
                Some(id) => id.pretty_print(out, context.interner)?,
            }
        }
        write!(out, " : ")?;

        self.ty.pretty_print(out, context)?;
        write!(out, ")")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::ParserTestExt;

    #[test]
    fn test_pi_type() {
        let mut interner = Interner::new();
        let id_u = Identifier::from_str("u", &mut interner);
        let id_a = Identifier::from_str("a", &mut interner);
        let id_nat = Identifier::from_str("Nat", &mut interner);

        let t1 = term().parse_all("u -> u", &mut interner);
        let TermKind::PiType { binder, output } = t1.kind else {
            panic!()
        };
        assert_eq!(binder.names, vec![None]);
        assert_eq!(
            binder.ty.kind,
            TermKind::Path(OwnedPath::from_id(id_u), LevelArgs::default())
        );
        assert_eq!(
            output.kind,
            TermKind::Path(OwnedPath::from_id(id_u), LevelArgs::default())
        );

        let t2 = term().parse_all("(a _ : Nat) -> u", &mut interner);
        let TermKind::PiType { binder, output } = t2.kind else {
            panic!()
        };
        assert_eq!(binder.names, vec![Some(id_a), None]);
        assert_eq!(
            binder.ty.kind,
            TermKind::Path(OwnedPath::from_id(id_nat), LevelArgs::default())
        );
        assert_eq!(
            output.kind,
            TermKind::Path(OwnedPath::from_id(id_u), LevelArgs::default())
        );
    }
}
