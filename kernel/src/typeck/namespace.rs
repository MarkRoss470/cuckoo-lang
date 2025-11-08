//! The [`Namespace`] type

use crate::typeck::error::TypeErrorKind;
use crate::typeck::level::LevelArgs;
use crate::typeck::term::TypedTerm;
use crate::typeck::{PrettyPrintContext, TypeError};
use common::{Identifier, PrettyPrint};
use parser::ast::item::LevelParameters;
use parser::atoms::ident::{OwnedPath, Path};
use parser::error::Span;
use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::io::Write;

/// A namespace which maps [`Path`]s to terms
#[derive(Debug, Default)]
pub struct Namespace {
    /// The entries of this namespace
    items: HashMap<Identifier, NamespaceItem>,
    /// The other namespaces which are children of this one
    namespaces: HashMap<Identifier, Namespace>,
}

/// An item in a [`Namespace`]
#[derive(Debug)]
struct NamespaceItem {
    /// The source span of the item which this namespace item represents
    span: Span,
    /// The level parameters of the item
    level_params: LevelParameters,
    /// The term which this namespace item represents
    value: TypedTerm,

    /// A cache of instantiations of [`value`] for different sets of [`LevelArgs`]. Used to
    /// avoid [instantiating] the term on the same arguments multiple times.
    ///
    /// [`value`]: NamespaceItem::value
    /// [instantiating]: TypedTerm::instantiate
    instantiation_cache: RefCell<HashMap<LevelArgs, TypedTerm>>,
}

impl Namespace {
    /// Constructs a new empty namespace
    pub fn new() -> Self {
        Default::default()
    }

    /// Resolves an identifier in the namespace
    fn resolve_ident(&self, id: Identifier, span: Span) -> Result<&NamespaceItem, Box<TypeError>> {
        match self.items.get(&id) {
            None => Err(Box::new(TypeError {
                span,
                kind: TypeErrorKind::NameNotResolved(OwnedPath::from_id(id)),
            })),
            Some(v) => Ok(v),
        }
    }

    /// Resolves a path to the [`NamespaceItem`] it represents
    fn resolve_inner(&self, path: Path, span: Span) -> Result<&NamespaceItem, Box<TypeError>> {
        let (id, rest) = path.split_first();

        match rest {
            None => self.resolve_ident(id, span.clone()),
            Some(rest) => match self.namespaces.get(&id) {
                None => Err(Box::new(TypeError {
                    span,
                    kind: TypeErrorKind::NameNotResolved(path.to_owned()),
                })),
                Some(n) => n
                    .resolve_inner(rest, span.clone())
                    .map_err(|e| match e.kind {
                        TypeErrorKind::NameNotResolved(p) => Box::new(TypeError {
                            span: span.clone(),
                            kind: TypeErrorKind::NameNotResolved(p.prepend(id)),
                        }),
                        _ => e,
                    }),
            },
        }
    }

    /// Resolves a path to the term it represents
    pub fn resolve(
        &self,
        path: Path,
        level_args: &LevelArgs,
        span: Span,
    ) -> Result<TypedTerm, Box<TypeError>> {
        let item = self.resolve_inner(path, span.clone())?;

        // Check that there are the right number of level arguments
        if item.level_params.count() != level_args.count() {
            Err(Box::new(TypeError {
                span,
                kind: TypeErrorKind::WrongNumberOfLevelArgs {
                    path: path.to_owned(),
                    expected: item.level_params.count(),
                    found: level_args.count(),
                },
            }))
        } else {
            // Normalize the level arguments for better cache hit rates
            let level_args = level_args.normalize();

            Ok(item.instantiate(level_args))
        }
    }

    /// Inserts an item into the namespace
    pub fn insert(
        &mut self,
        path: Path,
        level_params: LevelParameters,
        value: TypedTerm,
        span: Span,
    ) -> Result<(), Box<TypeError>> {
        let (id, rest) = path.split_first();

        let value = value.normalize_level();

        match rest {
            None => {
                // Check that there isn't already an item with this name
                if let Entry::Vacant(e) = self.items.entry(id) {
                    e.insert(NamespaceItem {
                        span,
                        level_params,
                        value,
                        instantiation_cache: RefCell::new(HashMap::new()),
                    });
                    Ok(())
                } else {
                    Err(Box::new(TypeError {
                        span,
                        kind: TypeErrorKind::NameAlreadyDefined(OwnedPath::from_id(id)),
                    }))
                }
            }
            Some(rest) => {
                // Add a new namespace if there isn't one already
                self.namespaces.entry(id).or_default();

                self.namespaces
                    .get_mut(&id)
                    .unwrap()
                    .insert(rest, level_params, value, span.clone())
                    .map_err(|e| match e.kind {
                        TypeErrorKind::NameAlreadyDefined(p) => Box::new(TypeError {
                            span,
                            kind: TypeErrorKind::NameAlreadyDefined(p.prepend(id)),
                        }),
                        _ => e,
                    })
            }
        }
    }

    /// If a namespace doesn't already exist at the given path, creates a new empty one.
    pub fn insert_namespace(&mut self, path: Path) {
        let (id, rest) = path.split_first();
        self.namespaces.entry(id).or_default();

        if let Some(r) = rest {
            let ns = self.namespaces.get_mut(&id).unwrap();
            ns.insert_namespace(r)
        }
    }

    /// Gets a reference to the namespace at `path`
    pub fn resolve_namespace(&self, path: Path, span: Span) -> Result<&Namespace, Box<TypeError>> {
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

    /// Gets a mutable reference to the namespace at `path`
    pub fn resolve_namespace_mut(
        &mut self,
        path: Path,
        span: Span,
    ) -> Result<&mut Namespace, Box<TypeError>> {
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

impl NamespaceItem {
    /// Instantiates the term with the given level arguments, without using the instantiation cache.
    fn instantiate_uncached(&self, level_args: &LevelArgs) -> TypedTerm {
        self.value.instantiate(level_args)
    }

    /// Instantiates the term with the given level arguments, using a cached version if possible.
    fn instantiate(&self, level_args: LevelArgs) -> TypedTerm {
        // If a read-only reference can't be acquired, just do the instantiation
        let Ok(cache) = self.instantiation_cache.try_borrow() else {
            return self.instantiate_uncached(&level_args);
        };
        // If the cache contains an entry for the given level arguments, return it
        if let Some(val) = cache.get(&level_args) {
            return val.clone();
        }

        // Drop the read-only reference so that it doesn't block us from acquiring a writable one
        drop(cache);
        let val = self.instantiate_uncached(&level_args);

        // Write the instantiation to the cache
        if let Ok(mut cache) = self.instantiation_cache.try_borrow_mut() {
            cache.insert(level_args, val.clone());
        }

        val
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
