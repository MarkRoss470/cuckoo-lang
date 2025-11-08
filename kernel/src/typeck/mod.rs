//! The [`TypingEnvironment`] and related types

mod context;
mod data;
mod error;
mod level;
mod namespace;
mod term;

pub use error::TypeError;
pub(crate) use term::TypedTerm;

use std::cell::{Ref, RefCell};

use crate::diagnostic::KernelError;
use crate::typeck::context::TypingContext;
use crate::typeck::data::Adt;
use crate::typeck::level::LevelArgs;
use crate::typeck::namespace::Namespace;
use crate::typeck::term::Abbreviation;
use common::{Interner, PrettyPrint};
use parser::SourceFile;
use parser::ast::item::axiom::AxiomDefinition;
use parser::ast::item::def::ValueDefinition;
use parser::ast::item::{Item, LevelParameters};
use parser::ast::term::{Term, TermKind};
use parser::ast::{Ast, parse_file};
use parser::atoms::ident::{OwnedPath, Path};
use parser::error::Span;
use std::io::Write;

/// A unique index which identifies an ADT
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct AdtIndex(usize);

/// A unique index which identifies an axiom
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct AxiomIndex(usize);

/// A typing environment which stores the ADTs, axioms, and value definitions which have been
/// defined so far. For the typing _context_ which also includes name resolution, see
/// [`TypingContext`]
#[derive(Debug)]
pub struct TypingEnvironment {
    /// The interner, used to convert between [`Identifier`]s and their string names
    ///
    /// [`Identifier`]: common::Identifier
    pub interner: RefCell<Interner>,
    /// The environment's configuration
    pub config: TypingEnvironmentConfig,
    /// Statistics about how many times certain operations have occurred, used for performance
    /// profiling and debugging
    #[cfg(feature = "track-stats")]
    pub stats: TypingEnvironmentStats,

    /// The ADTs which have been defined so far
    adts: Vec<Adt>,
    /// The root namespace
    root: Namespace,
    /// The paths to all defined axioms
    axioms: Vec<Axiom>,
    /// The level parameters of the item currently being type checked
    level_parameters: Option<LevelParameters>,
}

/// Configuration settings for a [`KernelEnvironment`]
///
/// [`KernelEnvironment`]: crate::KernelEnvironment
#[derive(Debug)]
pub struct TypingEnvironmentConfig {
    /// Whether to double-check the correctness of terms after they are produced
    pub check_terms: bool,
    /// The largest allowed level literal
    pub max_level_literal: usize,
}

impl Default for TypingEnvironmentConfig {
    fn default() -> Self {
        Self {
            check_terms: cfg!(any(debug_assertions, test)),
            max_level_literal: 8,
        }
    }
}

/// Statistics about how many times operations have occurred while type-checking a program
#[cfg(feature = "track-stats")]
#[derive(Debug, Default, Clone)]
pub struct TypingEnvironmentStats {
    /// The number of times [`check_term`] has been called on a term
    /// where the term has been checked before
    ///
    /// [`check_term`]: TypingEnvironment::check_term
    check_cache_hits: Cell<usize>,
    /// The number of times [`check_term`] has been called on a term
    /// where the term has not been checked before
    ///
    /// [`check_term`]: TypingEnvironment::check_term
    check_cache_misses: Cell<usize>,

    /// The number of [`def_eq`] calls
    ///
    /// [`def_eq`]: TypingEnvironment::def_eq
    def_eq_calls: Cell<usize>,
    /// The number of [`def_eq`] calls where the arguments were equivalent
    ///
    /// [`def_eq`]: TypingEnvironment::def_eq
    def_eq_equiv_hits: Cell<usize>,
    /// The number of [`def_eq`] calls where the arguments were equivalent
    ///
    /// [`def_eq`]: TypingEnvironment::def_eq
    def_eq_sort_literals: Cell<usize>,
    /// The number of [`def_eq`] calls where the arguments were proof terms
    ///
    /// [`def_eq`]: TypingEnvironment::def_eq
    def_eq_proof_terms: Cell<usize>,
    /// The number of [`def_eq`] calls where no special rules were applied and
    /// the arguments were genuinely checked
    ///
    /// [`def_eq`]: TypingEnvironment::def_eq
    def_eq_non_special_cases: Cell<usize>,
}

/// An axiom, defined using the `axiom` keyword
#[derive(Debug)]
pub struct Axiom {
    /// The index into [`TypingEnvironment::axioms`] where this axiom is stored
    index: AxiomIndex,
    /// The name of the axiom
    path: OwnedPath,
    /// The axiom's level parameters
    level_params: LevelParameters,
    /// The type of the axiom
    ty: TypedTerm,
}

impl Default for TypingEnvironment {
    fn default() -> Self {
        Self {
            interner: RefCell::new(Interner::new()),
            config: Default::default(),
            #[cfg(feature = "track-stats")]
            stats: Default::default(),
            adts: vec![],
            root: Namespace::new(),
            axioms: vec![],
            level_parameters: None,
        }
    }
}

impl TypingEnvironment {
    /// Gets a reference to the ADT with index `id`
    fn get_adt(&self, id: AdtIndex) -> &Adt {
        &self.adts[id.0]
    }

    /// Gets a reference to the axiom with index `id`
    fn get_axiom(&self, id: AxiomIndex) -> &Axiom {
        &self.axioms[id.0]
    }

    /// Resolves a path to the term it represents
    ///
    /// # Parameters
    /// * `path`: The path to look up
    /// * `level_args`: The level arguments given to the path
    /// * `span`: The source span to use for the returned term
    fn resolve_path(
        &self,
        path: Path,
        level_args: &LevelArgs,
        span: Span,
    ) -> Result<TypedTerm, Box<TypeError>> {
        self.root.resolve(path, level_args, span)
    }

    /// Typechecks a file. Any names defined by the file's contents will be stored in `self` and
    /// can be used by future files.
    pub fn load(&mut self, source: &SourceFile) -> Result<(), KernelError> {
        let res = parse_file(&mut self.interner.borrow_mut(), source);
        if !res.diagnostics.is_empty() {
            return Err(KernelError::Parse(
                res.diagnostics.into_iter().next().unwrap().value,
            ));
        }

        self.load_ast(&res.value).map_err(KernelError::Type)
    }

    /// Runs [`load`] on content from a string
    ///
    /// [`load`]: TypingEnvironment::load
    #[cfg(any(test, feature = "test-utils"))]
    pub fn load_str(&mut self, source: &str) -> Result<(), KernelError> {
        self.load(&SourceFile::test_source(source))
    }

    /// Resolves an AST one item at a time
    pub fn load_ast(&mut self, ast: &Ast) -> Result<(), Box<TypeError>> {
        for item in &ast.items {
            match item {
                Item::DataDefinition(dd) => self.resolve_adt(dd)?,
                Item::ValueDefinition(vd) => self.resolve_value_definition(vd)?,
                Item::Axiom(ad) => self.resolve_axiom_definition(ad)?,
                Item::Malformed(span) => {
                    Err(TypeError::unsupported(span.clone(), "Malformed items"))?
                }
            }
        }

        Ok(())
    }

    /// Resolves a `def` statement
    fn resolve_value_definition(&mut self, ast: &ValueDefinition) -> Result<(), Box<TypeError>> {
        let mut ty = ast.ty.clone();
        let mut value = ast.value.clone();

        // Set the level parameters for this item
        self.set_level_params(ast.level_params.clone())?;

        // Desugar `def` parameters to pi types and lambda expressions
        for binder in ast.binders.iter().rev() {
            ty = Term {
                span: ast.span.clone(),
                kind: TermKind::PiType {
                    binder: Box::new(binder.clone()),
                    output: Box::new(ty),
                },
            };

            value = Term {
                span: ast.span.clone(),
                kind: TermKind::Lambda {
                    binder: Box::new(binder.clone()),
                    body: Box::new(value),
                },
            };
        }

        // Resolve the type of the `def`
        let ty = TypingContext::Root(self).resolve_term(&ty)?;
        let level = ty.check_is_ty()?;

        // Resolve the value of the `def`
        let value = TypingContext::Root(self).resolve_term(&value)?;

        // Check that the value has the right type
        if !value.level().def_eq(&level) || !self.def_eq(ty.clone(), value.get_type()) {
            return Err(Box::new(self.mismatched_types_error(value, ty)));
        }

        let term = TypedTerm::value_of_type(value.term(), ty, value.span()).with_abbreviation(
            Abbreviation::Constant(
                ast.path.clone(),
                LevelArgs::from_level_parameters(&ast.level_params),
            ),
        );

        if self.config.check_terms {
            self.check_term(&term);
        }

        self.root.insert(
            ast.path.borrow(),
            ast.level_params.clone(),
            term,
            ast.span.clone(),
        )?;

        // Remove the level parameters from the context
        self.clear_level_params();

        Ok(())
    }

    /// Resolves an `axiom` definition
    fn resolve_axiom_definition(&mut self, ast: &AxiomDefinition) -> Result<(), Box<TypeError>> {
        let mut ty = ast.ty.clone();

        // Set the level parameters for this item
        self.set_level_params(ast.level_params.clone())?;

        // Desugar axiom parameters to pi types
        for binder in ast.binders.iter().rev() {
            ty = Term {
                span: ast.span.clone(),
                kind: TermKind::PiType {
                    binder: Box::new(binder.clone()),
                    output: Box::new(ty),
                },
            };
        }

        // Resolve the type of the axiom
        let ty = TypingContext::Root(self).resolve_term(&ty)?;

        let axiom = self.add_axiom(ast.path.clone(), ast.level_params.clone(), ty.clone());

        let term = TypedTerm::axiom(
            axiom.index,
            ty,
            LevelArgs::from_level_parameters(&ast.level_params),
            ast.span.clone(),
        );

        self.root.insert(
            ast.path.borrow(),
            ast.level_params.clone(),
            term,
            ast.span.clone(),
        )?;

        // Remove the level parameters from the context
        self.clear_level_params();

        Ok(())
    }

    /// Adds a new [`Axiom`] definition to the environment with the given properties, returning a
    /// reference to it.
    fn add_axiom(
        &mut self,
        path: OwnedPath,
        level_params: LevelParameters,
        ty: TypedTerm,
    ) -> &Axiom {
        let index = AxiomIndex(self.axioms.len());
        self.axioms.push(Axiom {
            index,
            path,
            level_params,
            ty,
        });
        self.axioms.last().unwrap()
    }
}

/// A context for pretty printing various objects
#[derive(Debug, Copy, Clone)]
pub struct PrettyPrintContext<'a> {
    /// The typing environment, mostly used for its [`interner`]
    ///
    /// [`interner`]: TypingEnvironment::interner
    environment: &'a TypingEnvironment,
    /// The indentation level that objects are currently being printed at
    indent_levels: usize,
    /// Whether to print proof terms
    print_proofs: bool,
}

impl<'a> PrettyPrintContext<'a> {
    /// Constructs a new [`PrettyPrintContext`] in the given `environment`
    pub(crate) fn new(environment: &'a TypingEnvironment) -> Self {
        Self {
            environment,
            indent_levels: 0,
            print_proofs: false,
        }
    }

    /// Gets the [`interner`] from the context's [`environment`]
    ///
    /// [`interner`]: TypingEnvironment::interner
    /// [`environment`]: PrettyPrintContext::environment
    fn interner(&self) -> Ref<'_, Interner> {
        self.environment.interner.borrow()
    }

    /// Writes a newline to `out`, followed by the appropriate indent specified by [`indent_levels`]
    ///
    /// [`indent_levels`]: PrettyPrintContext::indent_levels
    fn newline(&self, out: &mut dyn Write) -> std::io::Result<()> {
        writeln!(out)?;

        for _ in 0..self.indent_levels {
            write!(out, "  ")?;
        }

        Ok(())
    }

    /// Borrows the context, with [`indent_levels`] incremented by 1
    ///
    /// [`indent_levels`]: PrettyPrintContext::indent_levels
    fn borrow_indented(self) -> Self {
        Self {
            indent_levels: self.indent_levels + 1,
            ..self
        }
    }
}

impl<'a> TypingEnvironment {
    /// Pretty prints the environment to `stdout`
    pub fn pretty_print(&self) {
        let context = PrettyPrintContext::new(self);

        let mut stdout = std::io::stdout().lock();

        for adt in &self.adts {
            adt.pretty_print(&mut stdout, context).unwrap();
        }

        self.root.pretty_print(&mut stdout, context).unwrap();
        writeln!(stdout).unwrap();
    }

    /// Pretty prints a value to `stdout` followed by a newline
    pub fn pretty_println_val(&'a self, val: &impl PrettyPrint<PrettyPrintContext<'a>>) {
        let context = PrettyPrintContext::new(self);

        let mut stdout = std::io::stdout().lock();

        val.pretty_print(&mut stdout, context).unwrap();

        writeln!(stdout).unwrap();
    }

    /// Pretty prints a value to `stdout` followed by a newline,
    /// printing proof terms
    pub fn pretty_println_val_with_proofs(
        &'a self,
        val: &impl PrettyPrint<PrettyPrintContext<'a>>,
    ) {
        let mut context = PrettyPrintContext::new(self);
        context.print_proofs = true;

        let mut stdout = std::io::stdout().lock();

        val.pretty_print(&mut stdout, context).unwrap();

        writeln!(stdout).unwrap();
    }
}
