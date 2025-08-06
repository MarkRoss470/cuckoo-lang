use crate::parser::PrettyPrint;
use crate::parser::atoms::{Identifier, OwnedPath, Path};
use crate::typeck::term::TypedTerm;
use crate::typeck::{PrettyPrintContext, TypeError};
use std::collections::HashMap;
use std::io::Write;

#[derive(Debug, Default)]
pub struct Namespace {
    values: HashMap<Identifier, TypedTerm>,
    namespaces: HashMap<Identifier, Namespace>,
}

impl Namespace {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn resolve(&self, path: Path) -> Result<TypedTerm, TypeError> {
        let (id, rest) = path.split_first();

        match rest {
            None => match self.values.get(&id) {
                None => Err(TypeError::NameNotResolved(id)),
                Some(v) => Ok(v.clone()),
            },
            Some(rest) => match self.namespaces.get(&id) {
                None => Err(TypeError::NameAlreadyDefined(id)),
                Some(n) => n.resolve(rest),
            },
        }
    }

    pub fn insert(&mut self, path: Path, value: TypedTerm) -> Result<(), TypeError> {
        let (id, rest) = path.split_first();

        match rest {
            None => {
                if self.values.contains_key(&id) {
                    Err(TypeError::NameAlreadyDefined(id))
                } else {
                    self.values.insert(id, value);
                    Ok(())
                }
            }
            Some(rest) => {
                if !self.namespaces.contains_key(&id) {
                    self.namespaces.insert(id, Namespace::new());
                }

                self.namespaces.get_mut(&id).unwrap().insert(rest, value)
            }
        }
    }

    /// If a namespace doesn't already exist at the given path, creates a new empty one.
    pub fn insert_namespace(&mut self, path: Path) {
        let (id, rest) = path.split_first();
        if !self.namespaces.contains_key(&id) {
            self.namespaces.insert(id, Namespace::new());
        }

        let ns = self.namespaces.get_mut(&id).unwrap();
        if let Some(r) = rest {
            ns.insert_namespace(r)
        }
    }

    pub fn resolve_namespace_mut(&mut self, path: Path) -> Result<&mut Namespace, TypeError> {
        let (id, rest) = path.split_first();
        let ns = self
            .namespaces
            .get_mut(&id)
            .ok_or(TypeError::NameNotResolved(id))?;

        match rest {
            None => Ok(ns),
            Some(r) => ns.resolve_namespace_mut(r),
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
