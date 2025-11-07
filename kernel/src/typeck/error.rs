//! The [`TypeError`] and [`TypeErrorKind`] types

use crate::typeck::level::Level;
use crate::typeck::term::TypedTermKind;
use crate::typeck::{AdtIndex, PrettyPrintContext, TypedTerm, TypingEnvironment};
use common::{Identifier, PrettyPrint};
use parser::atoms::ident::OwnedPath;
use parser::error::Span;
use std::io::Write;
use std::rc::Rc;

/// An error which occurred during type checking
#[derive(Debug, Clone)]
pub struct TypeError {
    /// The source span where the error occurred
    pub span: Span,
    /// The type of error which occurred
    pub kind: TypeErrorKind,
}

#[derive(Debug, Clone)]
pub enum TypeErrorKind {
    /// A feature was encountered which is not supported in the kernel
    UnsupportedInKernel(&'static str),

    // ----- Term resolution errors
    /// The function of an [`Application`] term did not have a pi type
    ///
    /// [`Application`]: parser::ast::term::TermKind::Application
    NotAFunction(TypedTerm),
    /// A term was not a type which should have been
    NotAType(TypedTerm),
    /// A name could not be resolved
    NameNotResolved(OwnedPath),
    /// A term has a different type to what was expected
    MismatchedTypes {
        /// The term which had the wrong type
        term: TypedTerm,
        /// The type it was expected to have
        expected: TypedTerm,
    },
    /// The first segment of a [`Path`] term referenced a bound variable
    ///
    /// [`Path`]: parser::ast::term::TermKind::Path
    LocalVariableIsNotANamespace(OwnedPath),

    // ------ Level errors
    /// A level literal was encountered which was larger than the configured limit
    LevelLiteralTooBig(usize),
    /// An item defined the same level parameter more than once
    DuplicateLevelParameter(Identifier),
    /// A level parameter was referenced which was not defined
    LevelParameterNotFound(Identifier),
    /// The wrong number of level arguments were given to a constant
    WrongNumberOfLevelArgs {
        /// The path of the constant
        path: OwnedPath,
        /// How many arguments were expected
        expected: usize,
        /// How many arguments were given
        found: usize,
    },
    /// Level argument(s) were given for a bound variable
    LevelArgumentGivenForLocalVariable(Identifier),

    // ----- ADT declaration errors
    /// The family of an ADT was not a pi type ending in `Sort _`
    NotASortFamily(TypedTerm),
    /// The level of an ADT was not either guaranteed to be `Prop` or guaranteed to not be `Prop`
    MayOrMayNotBeProp(Level),
    /// The resultant type for a constructor was not the ADT it was associated with
    IncorrectConstructorResultantType {
        /// The name of the constructor
        name: Identifier,
        /// What the output was actually an application of
        found: TypedTerm,
        /// The ADT in question
        expected: AdtIndex,
    },
    /// The ADT being defined was referenced from a disallowed location in a constructor
    InvalidLocationForAdtNameInConstructor(AdtIndex),
    /// An ADT was used with a parameter different from how it was defined
    MismatchedAdtParameter {
        /// The term which was used as a parameter
        found: TypedTerm,
        /// The term which was expected for the value of the parameter
        expected: Rc<TypedTermKind>,
    },
    /// A constructor parameter had too high a level
    InvalidConstructorParameterLevel {
        /// The type of the parameter
        ty: TypedTerm,
        /// The level of the ADT
        adt_level: Level,
    },

    // ----- Naming errors
    /// A name was declared multiple times
    NameAlreadyDefined(OwnedPath),
}

impl TypeError {
    /// Constructs an [`UnsupportedInKernel`] error with the given span and message
    ///
    /// [`UnsupportedInKernel`]: TypeErrorKind::UnsupportedInKernel
    pub(crate) fn unsupported(span: Span, msg: &'static str) -> Self {
        Self {
            span,
            kind: TypeErrorKind::UnsupportedInKernel(msg),
        }
    }
}

impl TypingEnvironment {
    /// Constructs a [`MismatchedTypes`] error, [fully reducing] the given terms
    ///
    /// [`MismatchedTypes`]: TypeErrorKind::MismatchedTypes
    /// [fully reducing]: TypingEnvironment::fully_reduce
    pub fn mismatched_types_error(&self, term: TypedTerm, expected: TypedTerm) -> TypeError {
        TypeError {
            span: term.span(),
            kind: TypeErrorKind::MismatchedTypes {
                term: self.fully_reduce(term, false),
                expected: self.fully_reduce(expected, false),
            },
        }
    }
}

/// Pretty prints a term. If the term is a proof term, it will print it with `print_proofs = true`,
/// Otherwise it will use whatever the context has for `print_proofs`.
fn pretty_print_term_in_error(
    term: &TypedTerm,
    out: &mut dyn Write,
    context: PrettyPrintContext,
) -> std::io::Result<()> {
    // If the term in question is a proof, then set print_proofs to true when printing it
    if term.level().def_eq(&Level::zero()) {
        let mut context = context;
        context.print_proofs = true;
        term.pretty_print(out, context)
    } else {
        term.pretty_print(out, context)
    }
}

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for TypeError {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext,
    ) -> std::io::Result<()> {
        write!(out, "ERROR at {}: ", self.span)?;

        match &self.kind {
            TypeErrorKind::UnsupportedInKernel(msg) => write!(out, "Unsupported in kernel: {msg}"),

            // ----- Term resolution errors
            TypeErrorKind::NotAFunction(t) => {
                pretty_print_term_in_error(t, out, context)?;
                write!(out, " is not a function. It has type ")?;
                t.ty().pretty_print(out, context)?;
                write!(out, ".")
            }
            TypeErrorKind::NotAType(t) => {
                pretty_print_term_in_error(t, out, context)?;
                write!(out, " is not a type. It has type ")?;
                t.ty().pretty_print(out, context)?;
                write!(out, ", which is not a sort.")
            }
            TypeErrorKind::NameNotResolved(id) => {
                write!(out, "Could not resolve name '")?;
                id.pretty_print(out, &context.interner())?;
                write!(out, "'.")
            }
            TypeErrorKind::MismatchedTypes { term, expected } => {
                write!(out, "Expected\n  ")?;
                pretty_print_term_in_error(term, out, context)?;
                write!(out, "\nto have type\n  ")?;
                expected.term().pretty_print(out, context)?;
                write!(out, "\nbut it has type\n  ")?;
                term.ty().pretty_print(out, context)?;
                write!(out, "\n.")
            }
            TypeErrorKind::LocalVariableIsNotANamespace(path) => {
                write!(out, "Local variable ")?;
                path.pretty_print(out, &context.interner())?;
                write!(
                    out,
                    " is not a namespace and cannot be used as the start of a path expression."
                )
            }

            // ------ Level errors
            TypeErrorKind::LevelLiteralTooBig(l) => {
                write!(
                    out,
                    "Level literal {l} is too large: the largest allowed level literal is currently configured to be {}.",
                    context.environment.config.max_level_literal
                )
            }
            TypeErrorKind::DuplicateLevelParameter(id) => {
                write!(out, "Duplicate level parameter ")?;
                id.pretty_print(out, &context.interner())
            }
            TypeErrorKind::LevelParameterNotFound(p) => {
                write!(out, "Level ")?;
                p.pretty_print(out, &context.interner())?;
                write!(out, " not found")
            }
            TypeErrorKind::WrongNumberOfLevelArgs {
                path,
                expected,
                found,
            } => {
                path.pretty_print(out, &context.interner())?;
                write!(
                    out,
                    " takes {expected} level argument(s), but {found} were provided."
                )
            }
            TypeErrorKind::LevelArgumentGivenForLocalVariable(id) => {
                write!(out, "Local variable ")?;
                id.pretty_print(out, &context.interner())?;
                write!(out, " can't take level arguments")
            }

            // ----- ADT declaration errors
            TypeErrorKind::NotASortFamily(t) => {
                pretty_print_term_in_error(t, out, context)?;
                write!(out, " is not a sort or family of sorts.")
            }
            TypeErrorKind::MayOrMayNotBeProp(level) => {
                write!(
                    out,
                    "Inductive types must either always be in Prop or always not be in Prop, but the level"
                )?;
                context.borrow_indented().newline(out)?;
                level.pretty_print(out, context.borrow_indented())?;
                context.newline(out)?;
                write!(out, "could be either.")
            }
            TypeErrorKind::IncorrectConstructorResultantType {
                name,
                found,
                expected,
            } => {
                write!(out, "Invalid resultant type for constructor. Constructor ")?;
                name.pretty_print(out, &context.interner())?;
                write!(out, " should result in an application of\n  ")?;
                context
                    .environment
                    .get_adt(*expected)
                    .header
                    .name
                    .pretty_print(out, &context.interner())?;
                write!(out, "\nbut it results in an application of\n  ")?;
                found.term().pretty_print(out, context)
            }
            TypeErrorKind::InvalidLocationForAdtNameInConstructor(id) => {
                context
                    .environment
                    .get_adt(*id)
                    .header
                    .name
                    .pretty_print(out, &context.interner())?;
                write!(out, " cannot be referenced here. ")?;
                write!(
                    out,
                    "The inductive datatype being constructed can only be referenced in strictly positive positions."
                )
            }
            TypeErrorKind::MismatchedAdtParameter { found, expected } => {
                write!(out, "Mismatched inductive type parameter. Found ")?;
                pretty_print_term_in_error(found, out, context)?;
                write!(out, ", expected ")?;
                expected.pretty_print(out, context)
            }
            TypeErrorKind::InvalidConstructorParameterLevel { ty, adt_level } => {
                write!(
                    out,
                    "Invalid level for constructor parameter - this parameter is of type\n  "
                )?;
                ty.term().pretty_print(out, context.borrow_indented())?;
                write!(out, "\nat level\n  ")?;
                ty.check_is_ty()
                    .unwrap()
                    .pretty_print(out, context.borrow_indented())?;
                write!(
                    out,
                    "\nwhich is not less than or equal to the inductive type's level\n  "
                )?;
                adt_level.pretty_print(out, context.borrow_indented())?;
                writeln!(out)
            }

            // ----- Naming errors
            TypeErrorKind::NameAlreadyDefined(id) => {
                write!(out, "The name ")?;
                id.pretty_print(out, &context.interner())?;
                write!(out, " has already been defined.")
            }

            #[expect(unreachable_patterns)]
            _ => todo!(),
        }
    }
}
