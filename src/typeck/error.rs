use crate::parser::PrettyPrint;
use crate::parser::atoms::{Identifier, OwnedPath};
use crate::typeck::{AdtIndex, PrettyPrintContext, TypedTerm};
use std::io::Write;

// TODO: track error locations
#[derive(Debug)]
pub enum TypeError {
    // ----- Term resolution errors
    NotAFunction(TypedTerm),
    NotAType(TypedTerm),
    NameNotResolved(Identifier),
    MismatchedTypes {
        term: TypedTerm,
        expected: TypedTerm,
    },
    NotANamespace(OwnedPath),

    // ----- ADT declaration errors
    NotASortFamily(TypedTerm),
    /// The resultant type for a constructor was not the ADT it was associated with
    IncorrectConstructorResultantType {
        name: Identifier,
        found: TypedTerm,
        expected: AdtIndex,
    },
    /// The ADT being defined was referenced from a disallowed location in a constructor
    InvalidLocationForAdtNameInConstructor(AdtIndex),
    
    // Naming errors
    NameAlreadyDefined(Identifier),
}

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for TypeError {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext,
    ) -> std::io::Result<()> {
        write!(out, "ERROR: ")?;

        match self {
            TypeError::NotAFunction(t) => {
                t.term.pretty_print(out, context)?;
                write!(out, " is not a function. It has type ")?;
                t.ty.pretty_print(out, context)?;
                write!(out, ".")
            }
            TypeError::NotAType(t) => {
                t.term.pretty_print(out, context)?;
                write!(out, " is not a type. It has type ")?;
                t.ty.pretty_print(out, context)?;
                write!(out, ", which is not a sort.")
            }
            TypeError::NameNotResolved(id) => {
                write!(out, "Could not resolve name '")?;
                id.pretty_print(out, context.interner())?;
                write!(out, "'.")
            }
            TypeError::MismatchedTypes { term, expected } => {
                write!(out, "Expected ")?;
                term.term.pretty_print(out, context)?;
                write!(out, " to have type ")?;
                expected.term.pretty_print(out, context)?;
                write!(out, ", but it has type ")?;
                term.ty.pretty_print(out, context)?;
                write!(out, ".")
            }
            TypeError::NotASortFamily(t) => {
                t.term.pretty_print(out, context)?;
                write!(out, " is not a sort or family of sorts.")
            }
            TypeError::IncorrectConstructorResultantType {
                name,
                found,
                expected,
            } => {
                write!(out, "Invalid resultant type for constructor. Constructor ")?;
                name.pretty_print(out, context.interner())?;
                write!(out, " should result in an application of ")?;
                context
                    .environment
                    .get_adt(*expected)
                    .name
                    .pretty_print(out, context.interner())?;
                write!(out, ", but it results in ")?;
                found.term.pretty_print(out, context)
            }
            TypeError::InvalidLocationForAdtNameInConstructor(id) => {
                context
                    .environment
                    .get_adt(*id)
                    .name
                    .pretty_print(out, context.interner())?;
                write!(out, " cannot be referenced here. ")?;
                write!(
                    out,
                    "The inductive datatype being constructed can only be referenced in strictly positive positions. "
                )
            }
            TypeError::NameAlreadyDefined(id) => {
                write!(out, "The name ")?;
                id.pretty_print(out, context.interner())?;
                write!(out, " has already been defined.")
            }
            _ => todo!(),
        }
    }
}
