//! The [`TypedTerm`], [`TypedTermKind`], [`TypedBinder`], and related types

pub mod accessors;
mod check;
pub mod constructors;
pub mod def_eq;
mod equiv;
pub mod modifiers;
#[cfg(test)]
pub mod tests;

use crate::typeck::level::{Level, LevelArgs};
use crate::typeck::{AdtIndex, AxiomIndex, PrettyPrintContext};
use common::{Identifier, PrettyPrint};
use parser::atoms::ident::OwnedPath;
use parser::error::Span;
use std::cell::Cell;
use std::io::Write;
use std::rc::Rc;

/// A term and its computed type
#[derive(Debug, Clone)]
pub struct TypedTerm {
    /// The source location associated with this term
    span: Span,
    /// The universe level of this term's type. For example, `Nat.zero` has level `1`,
    /// and `Sort 2` has level `4`
    level: Level,
    /// The type of this term
    ty: Rc<TypedTermKind>,
    /// The term itself
    term: Rc<TypedTermKind>,
}

/// A wrapper around [`TypedTermKindInner`] which caches properties about the term and stores
/// an abbreviation with which the term may be represented.
#[derive(Debug, Clone)]
pub struct TypedTermKind {
    /// Cached properties about the term, used to prevent unnecessary work.
    cached_properties: CachedTermProperties,
    /// The actual value of the term
    inner: TypedTermKindInner,
    /// An abbreviation with which to print the term.
    /// This is used so that when a defined constant such as `Nat.rec` is referenced
    /// without being reduced in any way, it prints the name of the definition rather than its
    /// value. This has no effect on type checking.
    abbreviation: Option<Rc<Abbreviation>>,
}

/// A syntactic form that a term can take
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
    /// The bound variable of a lambda abstraction or pi type, using de Bruijn indices
    BoundVariable {
        /// The de Bruijn index of the variable, which is the number of binders between the
        /// definition of the variable and its use.
        ///
        /// For example, in the term `fun (x : Nat) (y : Nat) => Fin y -> Fin x`,
        /// the reference to `y` in `Fin y` would have index `0`, while the `x` in `Fin x`
        /// would have index `2` (`Fin y -> Fin x` is syntactic sugar for `(_ : Fin y) -> Fin x`,
        /// so the LHS still counts as a binder.
        index: usize,
        /// The name of the bound variable. This is for pretty printing only, and is not used
        /// for type checking to avoid captures.
        name: Option<Identifier>,
    },
    /// A function application
    Application {
        /// The function which is being applied
        function: TypedTerm,
        /// The argument which it is being applied to
        argument: TypedTerm,
    },
    /// A function / pi type
    PiType {
        /// The binder representing the input type
        binder: TypedBinder,
        /// The output type
        output: TypedTerm,
    },
    /// A lambda abstraction
    Lambda {
        /// The binder representing the input to the lambda
        binder: TypedBinder,
        /// The output of the lambda
        body: TypedTerm,
    },
}

/// The binder of a pi type or lambda abstraction
#[derive(Debug, Clone)]
pub struct TypedBinder {
    /// The source span of the binder
    pub span: Span,
    /// The name of the binder
    pub name: Option<Identifier>,
    /// The type of the binder
    pub ty: TypedTerm,
}

/// Cached properties about a [`TypedTermKind`]
#[derive(Debug, Clone)]
struct CachedTermProperties {
    /// Whether the term has been checked for correctness by [`check_term`].
    /// This is used to avoid checking the same term more than once.
    ///
    /// [`check_term`]: TypingEnvironment::check_term
    checked: Cell<bool>,
    /// All bound variables referenced by the term have index less than this value.
    /// This is used to avoid computing [`increment_above`] and [`replace_binder`]
    /// if it can be guaranteed that the output will be identical to the input.
    ///
    /// [`increment_above`]: TypedTerm::increment_above
    /// [`replace_binder`]: TypedTerm::replace_binder
    indices_less_than: usize,
    /// Whether the term mentions any level parameters. This is used to avoid computing
    /// [`instantiate`] if it can be guaranteed that the output will be identical to the input.
    ///
    /// [`instantiate`]: TypedTerm::instantiate
    mentions_level_parameter: bool,
}

/// An abbreviation with which to print a term
#[derive(Debug, Clone)]
pub enum Abbreviation {
    /// A defined constant such as `Nat.add`
    Constant(OwnedPath, LevelArgs),
    /// An application of another abbreviation to an argument
    Application(Rc<Abbreviation>, TypedTerm),
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
