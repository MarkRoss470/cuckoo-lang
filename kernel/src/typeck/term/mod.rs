pub mod accessors;
mod check;
pub mod constructors;
pub mod def_eq;
pub mod modifiers;
#[cfg(test)]
mod tests;

use crate::typeck::level::{Level, LevelArgs};
use crate::typeck::{AdtIndex, AxiomIndex, PrettyPrintContext};
use common::{Identifier, PrettyPrint};
use derivative::Derivative;
use parser::atoms::ident::OwnedPath;
use parser::error::Span;
use std::cell::Cell;
use std::io::Write;
use std::rc::Rc;

#[derive(Debug, Clone, Derivative)]
#[derivative(PartialEq)]
pub(crate) struct TypedTerm {
    /// Whether the term has been checked for correctness.
    /// This is used to avoid checking the same term more than once.
    #[derivative(PartialEq = "ignore")]
    checked: Cell<bool>,

    /// The source location associated with this term
    #[derivative(PartialEq = "ignore")]
    span: Span,
    /// The universe level of this term's type. For example, `Nat.zero` has level `1`,
    /// and `Sort 2` has level `4`
    level: Level,
    /// The type of this term
    ty: Rc<TypedTermKind>,
    /// The term itself
    term: Rc<TypedTermKind>,
}

#[derive(Debug, Clone, Derivative)]
#[derivative(PartialEq)]
pub struct TypedTermKind {
    inner: TypedTermKindInner,
    #[derivative(PartialEq = "ignore")]
    abbreviation: Option<Rc<Abbreviation>>,
}

#[derive(Debug, Clone, Derivative)]
#[derivative(PartialEq)]
enum TypedTermKindInner {
    /// The keywords `Sort n`, `Prop` or `Type n`
    SortLiteral(Level),
    /// The name of an ADT
    AdtName(AdtIndex, LevelArgs),
    /// The name of an ADT constructor
    AdtConstructor(AdtIndex, usize, LevelArgs),
    /// The recursor of an ADT
    AdtRecursor(AdtIndex, LevelArgs),
    /// An axiom
    Axiom(AxiomIndex, LevelArgs),
    /// The bound variable of a lambda abstraction, using de Bruijn indices
    BoundVariable {
        /// The de Bruijn index
        index: usize,
        /// The name of the bound variable. This is for pretty printing only, and is not used
        /// for type checking to avoid captures.
        #[derivative(PartialEq = "ignore")]
        name: Option<Identifier>,
    },
    /// A function application
    Application {
        function: TypedTerm,
        argument: TypedTerm,
    },
    /// A function / pi type
    PiType {
        binder: TypedBinder,
        output: TypedTerm,
    },
    /// A lambda abstraction
    Lambda {
        binder: TypedBinder,
        body: TypedTerm,
    },
}

#[derive(Debug, Clone, Derivative)]
#[derivative(PartialEq)]
pub struct TypedBinder {
    #[derivative(PartialEq = "ignore")]
    pub span: Span,
    #[derivative(PartialEq = "ignore")]
    pub name: Option<Identifier>,
    pub ty: TypedTerm,
}

#[derive(Debug, Clone)]
pub enum Abbreviation {
    Constant(OwnedPath, LevelArgs),
    Application(Rc<Abbreviation>, TypedTerm),
}

impl TypedTermKind {
    fn inner(&self) -> &TypedTermKindInner {
        &self.inner
    }

    fn clone_inner(&self) -> TypedTermKindInner {
        self.inner.clone()
    }
}

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for TypedTerm {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext,
    ) -> std::io::Result<()> {
        // Abbreviate proof terms if configured
        if !context.print_proofs && self.level.def_eq(&Level::zero()) {
            write!(out, "...")
        } else {
            // write!(out, "<")?;
            // self.term.pretty_print(out, context)?;
            // write!(out, " # ")?;
            // self.ty.pretty_print(out, context)?;
            // write!(out, ">")

            self.term.pretty_print(out, context)
        }
    }
}

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for Abbreviation {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext<'a>,
    ) -> std::io::Result<()> {
        match self {
            Abbreviation::Constant(path, level_args) => {
                path.pretty_print(out, &context.interner())?;
                level_args.pretty_print(out, context)
            }
            Abbreviation::Application(abbr, term) => {
                write!(out, "(")?;
                abbr.pretty_print(out, context)?;
                write!(out, " ")?;
                term.pretty_print(out, context)?;
                write!(out, ")")
            }
        }
    }
}

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for TypedTermKind {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext,
    ) -> std::io::Result<()> {
        use TypedTermKindInner::*;

        if let Some(abbr) = &self.abbreviation {
            return abbr.pretty_print(out, context);
        }

        match self.inner() {
            SortLiteral(u) => {
                write!(out, "Sort ")?;
                u.pretty_print(out, context)
            }

            AdtName(adt, level_args) => {
                context
                    .environment
                    .get_adt(*adt)
                    .header
                    .name
                    .pretty_print(out, &context.interner())?;
                level_args.pretty_print(out, context)
            }
            AdtConstructor(adt, constructor, level_args) => {
                let adt = context.environment.get_adt(*adt);

                adt.header.name.pretty_print(out, &context.interner())?;
                write!(out, ".")?;
                adt.constructors[*constructor]
                    .name
                    .pretty_print(out, &context.interner())?;
                level_args.pretty_print(out, context)
            }
            AdtRecursor(adt, level_args) => {
                context
                    .environment
                    .get_adt(*adt)
                    .header
                    .name
                    .pretty_print(out, &context.interner())?;
                write!(out, ".rec")?;
                level_args.pretty_print(out, context)
            }
            Axiom(axiom, level_args) => {
                context
                    .environment
                    .get_axiom(*axiom)
                    .path
                    .pretty_print(out, &context.interner())?;
                level_args.pretty_print(out, context)
            }
            BoundVariable { index, name } => {
                match name {
                    None => write!(out, "_")?,
                    Some(name) => name.pretty_print(out, &context.interner())?,
                }
                write!(out, "?{index}")
            }
            Application { function, argument } => {
                write!(out, "(")?;
                function.pretty_print(out, context)?;
                write!(out, " ")?;
                argument.pretty_print(out, context)?;
                write!(out, ")")
            }
            PiType { binder, output } => {
                write!(out, "(")?;
                binder.pretty_print(out, context)?;
                write!(out, " -> ")?;
                output.pretty_print(out, context)?;
                write!(out, ")")
            }
            Lambda { binder, body } => {
                write!(out, "(fun ")?;
                binder.pretty_print(out, context)?;
                write!(out, " => ")?;
                body.pretty_print(out, context)?;
                write!(out, ")")
            }
        }
    }
}

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for TypedBinder {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext<'a>,
    ) -> std::io::Result<()> {
        write!(out, "(")?;

        match self.name {
            None => write!(out, "_")?,
            Some(id) => id.pretty_print(out, &context.interner())?,
        };

        write!(out, ": ")?;
        self.ty.pretty_print(out, context)?;

        write!(out, ")")
    }
}
