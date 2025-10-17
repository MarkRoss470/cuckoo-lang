use crate::typeck::level::Level;
use crate::typeck::term::TypedTermKind;
use crate::typeck::{AdtIndex, PrettyPrintContext, TypedTerm, TypingEnvironment};
use std::io::Write;
use common::{Identifier, PrettyPrint};
use parser::atoms::ident::OwnedPath;

// TODO: track error locations
#[cfg_attr(any(test, debug_assertions), derive(PartialEq))]
#[derive(Debug, Clone)]
pub enum TypeError {
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
        expected: TypedTermKind,
    },
    InvalidConstructorParameterLevel {
        ty: TypedTerm,
        adt_level: Level,
    },

    // ----- Naming errors
    NameAlreadyDefined(Identifier),
}

impl TypingEnvironment {
    pub fn mismatched_types_error(&self, term: TypedTerm, expected: TypedTerm) -> TypeError {
        TypeError::MismatchedTypes {
            term: self.fully_reduce(term, false),
            expected: self.fully_reduce(expected, false),
        }
    }
}

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for TypeError {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext,
    ) -> std::io::Result<()> {
        write!(out, "ERROR: ")?;

        match self {
            // ----- Term resolution errors
            TypeError::NotAFunction(t) => {
                t.term().pretty_print(out, context)?;
                write!(out, " is not a function. It has type ")?;
                t.ty().pretty_print(out, context)?;
                write!(out, ".")
            }
            TypeError::NotAType(t) => {
                t.term().pretty_print(out, context)?;
                write!(out, " is not a type. It has type ")?;
                t.ty().pretty_print(out, context)?;
                write!(out, ", which is not a sort.")
            }
            TypeError::NameNotResolved(id) => {
                write!(out, "Could not resolve name '")?;
                id.pretty_print(out, &context.interner())?;
                write!(out, "'.")
            }
            TypeError::MismatchedTypes { term, expected } => {
                write!(out, "Expected\n  ")?;
                term.term().pretty_print(out, context)?;
                write!(out, "\nto have type\n  ")?;
                expected.term().pretty_print(out, context)?;
                write!(out, "\nbut it has type\n  ")?;
                term.ty().pretty_print(out, context)?;
                write!(out, "\n.")
            }
            TypeError::LocalVariableIsNotANamespace(path) => {
                write!(out, "Local variable ")?;
                path.pretty_print(out, &context.interner())?;
                write!(
                    out,
                    " is not a namespace and cannot be used as the start of a path expression."
                )
            }

            // ------ Level errors
            TypeError::LevelLiteralTooBig(l) => {
                write!(
                    out,
                    "Level literal {l} is too large: level literals must be smaller than 8."
                )
            }
            TypeError::DuplicateLevelParameter(id) => {
                write!(out, "Duplicate level parameter ")?;
                id.pretty_print(out, &context.interner())
            }
            TypeError::LevelParameterNotFound(p) => {
                write!(out, "Level ")?;
                p.pretty_print(out, &context.interner())?;
                write!(out, " not found")
            }
            TypeError::WrongNumberOfLevelArgs {
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
            TypeError::LevelArgumentGivenForLocalVariable(id) => {
                write!(out, "Local variable ")?;
                id.pretty_print(out, &context.interner())?;
                write!(out, " can't take level arguments")
            }

            // ----- ADT declaration errors
            TypeError::NotASortFamily(t) => {
                t.term().pretty_print(out, context)?;
                write!(out, " is not a sort or family of sorts.")
            }
            TypeError::MayOrMayNotBeProp(level) => {
                write!(
                    out,
                    "Inductive types must either always be in Prop or always not be in Prop, but the level "
                )?;
                context.borrow_indented().newline(out)?;
                level.pretty_print(out, context.borrow_indented())?;
                context.newline(out)?;
                write!(out, "could be either.")
            }
            TypeError::IncorrectConstructorResultantType {
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
            TypeError::InvalidLocationForAdtNameInConstructor(id) => {
                context
                    .environment
                    .get_adt(*id)
                    .header
                    .name
                    .pretty_print(out, &context.interner())?;
                write!(out, " cannot be referenced here. ")?;
                write!(
                    out,
                    "The inductive datatype being constructed can only be referenced in strictly positive positions. "
                )
            }
            TypeError::MismatchedAdtParameter { found, expected } => {
                write!(out, "Mismatched inductive type parameter. Found ")?;
                found.term().pretty_print(out, context)?;
                write!(out, ", expected ")?;
                expected.pretty_print(out, context)
            }
            TypeError::InvalidConstructorParameterLevel { ty, adt_level } => {
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
            TypeError::NameAlreadyDefined(id) => {
                write!(out, "The name ")?;
                id.pretty_print(out, &context.interner())?;
                write!(out, " has already been defined.")
            }

            #[expect(unreachable_patterns)]
            _ => todo!(),
        }
    }
}
