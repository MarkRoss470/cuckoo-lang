use crate::typeck::level::Level;
use crate::typeck::term::TypedTermKind;
use crate::typeck::{AdtIndex, PrettyPrintContext, TypedTerm, TypingEnvironment};
use common::{Identifier, PrettyPrint};
use parser::atoms::ident::OwnedPath;
use parser::error::Span;
use std::io::Write;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct TypeError {
    pub span: Span,
    pub kind: TypeErrorKind,
}

#[derive(Debug, Clone)]
pub enum TypeErrorKind {
    /// A feature was encountered which is not supported in the kernel
    UnsupportedInKernel(&'static str),

    // ----- Term resolution errors
    NotAFunction(TypedTerm),
    NotAType(TypedTerm),
    NameNotResolved(OwnedPath),
    MismatchedTypes {
        term: TypedTerm,
        expected: TypedTerm,
    },
    LocalVariableIsNotANamespace(OwnedPath),

    // ------ Level errors
    LevelLiteralTooBig(usize),
    DuplicateLevelParameter(Identifier),
    LevelParameterNotFound(Identifier),
    WrongNumberOfLevelArgs {
        path: OwnedPath,
        expected: usize,
        found: usize,
    },
    LevelArgumentGivenForLocalVariable(Identifier),

    // ----- ADT declaration errors
    NotASortFamily(TypedTerm),
    MayOrMayNotBeProp(Level),
    /// The resultant type for a constructor was not the ADT it was associated with
    IncorrectConstructorResultantType {
        name: Identifier,
        found: TypedTerm,
        expected: AdtIndex,
    },
    /// The ADT being defined was referenced from a disallowed location in a constructor
    InvalidLocationForAdtNameInConstructor(AdtIndex),
    MismatchedAdtParameter {
        found: TypedTerm,
        expected: Rc<TypedTermKind>,
    },
    InvalidConstructorParameterLevel {
        ty: TypedTerm,
        adt_level: Level,
    },

    // ----- Naming errors
    NameAlreadyDefined(OwnedPath),
}

impl TypeError {
    pub(crate) fn unsupported(span: Span, msg: &'static str) -> Self {
        Self {
            span,
            kind: TypeErrorKind::UnsupportedInKernel(msg),
        }
    }
}

impl TypingEnvironment {
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
        let mut context = context.clone();
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
                    "Level literal {l} is too large: level literals must be at most 8."
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
                write!(out, " should result in an application of ")?;
                context
                    .environment
                    .get_adt(*expected)
                    .header
                    .name
                    .pretty_print(out, &context.interner())?;
                write!(out, ", but it results in ")?;
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
