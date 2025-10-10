use crate::parser::PrettyPrint;
use crate::parser::ast::item::LevelParameters;
use crate::parser::atoms::ident::{Identifier, OwnedPath, Path};
use crate::typeck::level::LevelArgs;
use crate::typeck::term::TypedTerm;
use crate::typeck::{PrettyPrintContext, TypeError};
use std::collections::HashMap;
use std::io::Write;

#[derive(Debug)]
struct NamespaceItem {
    level_params: LevelParameters,
    value: TypedTerm,
}

#[derive(Debug, Default)]
pub struct Namespace {
    items: HashMap<Identifier, NamespaceItem>,
    namespaces: HashMap<Identifier, Namespace>,
}

impl Namespace {
    pub fn new() -> Self {
        Default::default()
    }

    fn resolve_inner(&self, path: Path) -> Result<&NamespaceItem, TypeError> {
        let (id, rest) = path.split_first();

        match rest {
            None => match self.items.get(&id) {
                None => Err(TypeError::NameNotResolved(path.to_owned())),
                Some(v) => Ok(v),
            },
            Some(rest) => match self.namespaces.get(&id) {
                None => Err(TypeError::NameNotResolved(path.to_owned())),
                Some(n) => n.resolve_inner(rest.clone()).map_err(|e| match e {
                    TypeError::NameNotResolved(p) => TypeError::NameNotResolved(p.prepend(id)),
                    _ => e,
                }),
            },
        }
    }

    pub fn resolve(&self, path: Path, level_args: &LevelArgs) -> Result<TypedTerm, TypeError> {
        let item = self.resolve_inner(path)?;

        // Check that there are the right number of level arguments
        if item.level_params.count() != level_args.count() {
            Err(TypeError::WrongNumberOfLevelArgs {
                path: path.to_owned(),
                expected: item.level_params.count(),
                found: level_args.count(),
            })
        } else {
            Ok(item.value.instantiate(level_args))
        }
    }

    pub fn resolve_ty(&self, path: Path, level_args: &LevelArgs) -> Result<TypedTerm, TypeError> {
        let item = self.resolve_inner(path)?;

        // Check that there are the right number of level arguments
        if item.level_params.count() != level_args.count() {
            Err(TypeError::WrongNumberOfLevelArgs {
                path: path.to_owned(),
                expected: item.level_params.count(),
                found: level_args.count(),
            })
        } else {
            Ok(item.value.get_type().instantiate(level_args))
        }
    }

    pub fn insert(
        &mut self,
        path: Path,
        level_params: LevelParameters,
        value: TypedTerm,
    ) -> Result<(), TypeError> {
        let (id, rest) = path.split_first();

        match rest {
            None => {
                if self.items.contains_key(&id) {
                    Err(TypeError::NameAlreadyDefined(id))
                } else {
                    self.items.insert(
                        id,
                        NamespaceItem {
                            level_params,
                            value,
                        },
                    );
                    Ok(())
                }
            }
            Some(rest) => {
                if !self.namespaces.contains_key(&id) {
                    self.namespaces.insert(id, Namespace::new());
                }

                self.namespaces
                    .get_mut(&id)
                    .unwrap()
                    .insert(rest, level_params, value)
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
            .ok_or(TypeError::NameNotResolved(OwnedPath::from_id(id)))?;

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
        for (id, item) in &self.items {
            context.newline(out)?;
            write!(out, "def ")?;
            id.pretty_print(out, &context.interner())?;
            item.level_params.pretty_print(out, &context.interner())?;
            write!(out, " : ")?;
            item.value.ty().pretty_print(out, context)?;
            write!(out, " := ")?;
            item.value.term().pretty_print(out, context)?;
        }

        for (id, namespace) in &self.namespaces {
            context.newline(out)?;
            context.newline(out)?;

            write!(out, "namespace ")?;
            id.pretty_print(out, &context.interner())?;

            namespace.pretty_print(out, context.borrow_indented())?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_resolve_path() {
        todo!()
    }
}
