use crate::typeck::error::TypeErrorKind;
use crate::typeck::level::LevelArgs;
use crate::typeck::term::TypedTerm;
use crate::typeck::{PrettyPrintContext, TypeError};
use common::{Identifier, PrettyPrint};
use parser::ast::item::LevelParameters;
use parser::ast::term::LevelExprKind::Parameter;
use parser::atoms::ident::{OwnedPath, Path};
use parser::error::Span;
use std::collections::HashMap;
use std::io::Write;

#[derive(Debug)]
struct NamespaceItem {
    span: Span,
    level_params: LevelParameters,
    value: TypedTerm,

    instantiation_cache: HashMap<LevelArgs, TypedTerm>,
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

    fn resolve_inner(&self, path: Path, span: Span) -> Result<&NamespaceItem, TypeError> {
        let (id, rest) = path.split_first();

        match rest {
            None => self.resolve_ident(id, span.clone()),
            Some(rest) => match self.namespaces.get(&id) {
                None => Err(TypeError {
                    span,
                    kind: TypeErrorKind::NameNotResolved(path.to_owned()),
                }),
                Some(n) => n
                    .resolve_inner(rest.clone(), span.clone())
                    .map_err(|e| match e.kind {
                        TypeErrorKind::NameNotResolved(p) => TypeError {
                            span: span.clone(),
                            kind: TypeErrorKind::NameNotResolved(p.prepend(id)),
                        },
                        _ => e,
                    }),
            },
        }
    }

    fn resolve_ident(&self, id: Identifier, span: Span) -> Result<&NamespaceItem, TypeError> {
        match self.items.get(&id) {
            None => Err(TypeError {
                span,
                kind: TypeErrorKind::NameNotResolved(OwnedPath::from_id(id)),
            }),
            Some(v) => Ok(v),
        }
    }

    pub fn resolve(
        &self,
        path: Path,
        level_args: &LevelArgs,
        span: Span,
    ) -> Result<TypedTerm, TypeError> {
        let item = self.resolve_inner(path, span.clone())?;

        // Check that there are the right number of level arguments
        if item.level_params.count() != level_args.count() {
            Err(TypeError {
                span,
                kind: TypeErrorKind::WrongNumberOfLevelArgs {
                    path: path.to_owned(),
                    expected: item.level_params.count(),
                    found: level_args.count(),
                },
            })
        } else {
            Ok(item.value.instantiate(level_args))
        }
    }

    pub fn resolve_ty(
        &self,
        path: Path,
        level_args: &LevelArgs,
        span: Span,
    ) -> Result<TypedTerm, TypeError> {
        let item = self.resolve_inner(path, span.clone())?;

        // Check that there are the right number of level arguments
        if item.level_params.count() != level_args.count() {
            Err(TypeError {
                span,
                kind: TypeErrorKind::WrongNumberOfLevelArgs {
                    path: path.to_owned(),
                    expected: item.level_params.count(),
                    found: level_args.count(),
                },
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
        span: Span,
    ) -> Result<(), TypeError> {
        let (id, rest) = path.split_first();

        let value = value.normalize_level();

        match rest {
            None => {
                if self.items.contains_key(&id) {
                    Err(TypeError {
                        span,
                        kind: TypeErrorKind::NameAlreadyDefined(id),
                    })
                } else {
                    self.items.insert(
                        id,
                        NamespaceItem {
                            span,
                            level_params,
                            value,
                            instantiation_cache: HashMap::new(),
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
                    .insert(rest, level_params, value, span)
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

    pub fn resolve_namespace(&self, path: Path, span: Span) -> Result<&Namespace, TypeError> {
        let (id, rest) = path.split_first();
        let ns = self.namespaces.get(&id).ok_or(TypeError {
            span: span.clone(),
            kind: TypeErrorKind::NameNotResolved(OwnedPath::from_id(id)),
        })?;

        match rest {
            None => Ok(ns),
            Some(r) => ns.resolve_namespace(r, span),
        }
    }

    pub fn resolve_namespace_mut(
        &mut self,
        path: Path,
        span: Span,
    ) -> Result<&mut Namespace, TypeError> {
        let (id, rest) = path.split_first();
        let ns = self.namespaces.get_mut(&id).ok_or(TypeError {
            span: span.clone(),
            kind: TypeErrorKind::NameNotResolved(OwnedPath::from_id(id)),
        })?;

        match rest {
            None => Ok(ns),
            Some(r) => ns.resolve_namespace_mut(r, span),
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
            item.value
                .term()
                .clear_abbreviation()
                .pretty_print(out, context)?;
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
