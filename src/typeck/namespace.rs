use std::collections::HashMap;
use std::io::Write;
use crate::parser::atoms::Identifier;
use crate::parser::PrettyPrint;
use crate::typeck::term::TypedTerm;
use crate::typeck::{PrettyPrintContext, TypeError};

#[derive(Debug, Default)]
pub struct Namespace {
    values: HashMap<Identifier, TypedTerm>,
}

impl Namespace {
    pub fn new() -> Self {
        Default::default()
    }
    
    pub fn resolve_identifier(&self, id: Identifier) -> Result<TypedTerm, TypeError> {
        self.values
            .get(&id)
            .cloned()
            .ok_or(TypeError::NameNotResolved(id))
    }

    pub fn insert(&mut self, id: Identifier, value: TypedTerm) -> Result<(), TypeError> {
        match self.values.insert(id, value) {
            None => Ok(()),
            Some(_) => Err(TypeError::NameAlreadyDefined(id)),
        }
    }
}

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for Namespace {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext<'a>,
    ) -> std::io::Result<()> {
        for (id, val) in &self.values {
            write!(out, "def ")?;
            id.pretty_print(out, context.interner())?;
            write!(out, " : ")?;
            val.ty.pretty_print(out, context)?;
            write!(out, " := ")?;
            val.term.pretty_print(out, context)?;
            writeln!(out)?;
        }

        Ok(())
    }
}