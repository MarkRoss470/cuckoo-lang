use std::io::Write;
use crate::parser::atoms::Identifier;
use crate::parser::{PrettyPrint};
use crate::typeck::{PrettyPrintContext, TypedTerm};

#[derive(Debug)]
pub enum TypeError {
    NotAFunction(TypedTerm),
    NotAType(TypedTerm),
    NameNotResolved(Identifier),
    MismatchedTypes {
        term: TypedTerm,
        expected: TypedTerm,
    },
}

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for TypeError {
    fn pretty_print(&self, out: &mut dyn Write, context: PrettyPrintContext) -> std::io::Result<()> {
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
        }
    }
}