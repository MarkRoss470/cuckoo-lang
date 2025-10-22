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
use parser::atoms::ident::OwnedPath;
use parser::error::Span;
use std::io::Write;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub(crate) struct TypedTerm {
    span: Span,
    level: Level,
    ty: TypedTermKind,
    term: TypedTermKind,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedTermKind {
    inner: Rc<TypedTermKindInner>,
    abbreviation: Option<Rc<Abbreviation>>,
}

#[derive(Debug, Clone)]
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
        /// The name of the bound variable. This is for pretty printing only, and should not be used
        /// for type checking to avoid captures.
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

#[derive(Debug, Clone)]
pub struct TypedBinder {
    pub span: Span,
    pub name: Option<Identifier>,
    pub ty: TypedTerm,
}

#[derive(Debug, Clone)]
pub enum Abbreviation {
    Constant(OwnedPath, LevelArgs),
    Application(Rc<Abbreviation>, TypedTerm),
}

impl PartialEq for TypedTerm {
    fn eq(&self, other: &Self) -> bool {
        self.level == other.level && self.ty == other.ty && self.term == other.term
    }
}

impl PartialEq for Abbreviation {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl PartialEq for TypedTermKindInner {
    fn eq(&self, other: &Self) -> bool {
        use TypedTermKindInner::*;

        match (self, other) {
            (SortLiteral(l1), SortLiteral(l2)) => l1 == l2,
            (SortLiteral(_), _) => false,
            (AdtName(a1, l1), AdtName(a2, l2)) => a1 == a2 && l1 == l2,
            (AdtName(_, _), _) => false,
            (AdtConstructor(a1, c1, l1), AdtConstructor(a2, c2, l2)) => {
                a1 == a2 && c1 == c2 && l1 == l2
            }
            (AdtConstructor(_, _, _), _) => false,
            (AdtRecursor(a1, l1), AdtRecursor(a2, l2)) => a1 == a2 && l1 == l2,
            (AdtRecursor(_, _), _) => false,
            (Axiom(a1, l1), Axiom(a2, l2)) => a1 == a2 && l1 == l2,
            (Axiom(_, _), _) => false,
            (BoundVariable { index: i1, name: _ }, BoundVariable { index: i2, name: _ }) => {
                i1 == i2
            }
            (BoundVariable { .. }, _) => false,
            (
                Application {
                    function: f1,
                    argument: a1,
                },
                Application {
                    function: f2,
                    argument: a2,
                },
            ) => f1 == f2 && a1 == a2,
            (Application { .. }, _) => false,
            (
                PiType {
                    binder: b1,
                    output: o1,
                },
                PiType {
                    binder: b2,
                    output: o2,
                },
            ) => b1 == b2 && o1 == o2,
            (PiType { .. }, _) => false,
            (
                Lambda {
                    binder: b1,
                    body: bo1,
                },
                Lambda {
                    binder: b2,
                    body: bo2,
                },
            ) => b1 == b2 && bo1 == bo2,
            (Lambda { .. }, _) => false,
        }
    }
}

impl PartialEq for TypedBinder {
    fn eq(&self, other: &Self) -> bool {
        self.ty == other.ty
    }
}

impl TypedTermKind {
    fn inner(&self) -> &TypedTermKindInner {
        self.inner.as_ref()
    }

    fn clone_inner(&self) -> TypedTermKindInner {
        self.inner.as_ref().clone()
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
