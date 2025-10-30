mod context;
mod data;
mod error;
mod level;
mod namespace;
mod term;

pub use error::TypeError;
pub(crate) use term::TypedTerm;

use std::cell::{Cell, Ref, RefCell};

use crate::diagnostic::KernelError;
use crate::typeck::data::Adt;
use crate::typeck::level::LevelArgs;
use crate::typeck::namespace::Namespace;
use crate::typeck::term::{Abbreviation, TypedBinder};
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
use std::sync::atomic::AtomicUsize;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct AdtIndex(usize);

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct AxiomIndex(usize);

#[derive(Debug)]
pub struct TypingEnvironment {
    pub interner: RefCell<Interner>,
    pub config: TypingEnvironmentConfig,
    pub stats: TypingEnvironmentStats,

    adts: Vec<Adt>,
    root: Namespace,
    /// The paths to all defined axioms
    axioms: Vec<Axiom>,
    /// The level parameters of the item currently being type checked
    level_parameters: Option<LevelParameters>,
}

#[derive(Debug)]
pub struct TypingEnvironmentConfig {
    /// Whether to double-check the correctness of terms after they are produced
    pub check_terms: bool,
}

impl Default for TypingEnvironmentConfig {
    fn default() -> Self {
        Self {
            check_terms: cfg!(any(debug_assertions, test)),
        }
    }
}

#[derive(Debug, Default)]
pub struct TypingEnvironmentStats {
    check_cache_hits: Cell<usize>,
    check_cache_misses: Cell<usize>,
}

#[derive(Debug)]
pub struct Axiom {
    index: AxiomIndex,
    path: OwnedPath,
    level_params: LevelParameters,
    ty: TypedTerm,
}

impl TypingEnvironment {
    pub fn new() -> Self {
        Self {
            interner: RefCell::new(Interner::new()),
            config: Default::default(),
            stats: Default::default(),
            adts: vec![],
            root: Namespace::new(),
            axioms: vec![],
            level_parameters: None,
        }
    }

    pub fn load(&mut self, source: &SourceFile) -> Result<(), KernelError> {
        let res = parse_file(&mut self.interner.borrow_mut(), source);
        if !res.diagnostics.is_empty() {
            return Err(KernelError::Parse(
                res.diagnostics.into_iter().next().unwrap().value,
            ));
        }

        self.load_ast(&res.value).map_err(KernelError::Type)
    }

    #[cfg(any(test, feature = "test-utils"))]
    pub fn load_str(&mut self, source: &str) -> Result<(), KernelError> {
        self.load(&SourceFile::test_source(source))
    }

    fn get_adt(&self, id: AdtIndex) -> &Adt {
        &self.adts[id.0]
    }

    fn get_axiom(&self, id: AxiomIndex) -> &Axiom {
        &self.axioms[id.0]
    }

    fn resolve_path(
        &self,
        path: Path,
        level_args: &LevelArgs,
        span: Span,
    ) -> Result<TypedTerm, TypeError> {
        self.root.resolve(path, level_args, span)
    }

    pub fn load_ast(&mut self, ast: &Ast) -> Result<(), TypeError> {
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

    fn resolve_value_definition(&mut self, ast: &ValueDefinition) -> Result<(), TypeError> {
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
            return Err(self.mismatched_types_error(value, ty));
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

    fn resolve_axiom_definition(&mut self, ast: &AxiomDefinition) -> Result<(), TypeError> {
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
}

#[derive(Debug, Copy, Clone)]
enum TypingContext<'a> {
    Root(&'a TypingEnvironment),
    Binders {
        /// The binders applied by this context. These are in source order, so later ones may
        /// depend on earlier ones.
        binders: &'a [TypedBinder],
        parent: &'a TypingContext<'a>,
    },
}

impl<'a> TypingContext<'a> {
    pub fn with_binder(&'a self, binder: &'a TypedBinder) -> Self {
        Self::Binders {
            binders: std::slice::from_ref(binder),
            parent: self,
        }
    }

    pub fn with_binders(&'a self, binders: &'a [TypedBinder]) -> Self {
        Self::Binders {
            binders,
            parent: self,
        }
    }

    fn environment(&self) -> &TypingEnvironment {
        match self {
            TypingContext::Root(env) => env,
            TypingContext::Binders { binders: _, parent } => parent.environment(),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct PrettyPrintContext<'a> {
    environment: &'a TypingEnvironment,
    indent_levels: usize,
    print_proofs: bool,
}

impl<'a> PrettyPrintContext<'a> {
    pub(crate) fn new(environment: &'a TypingEnvironment) -> Self {
        Self {
            environment,
            indent_levels: 0,
            print_proofs: false,
        }
    }

    fn interner(&self) -> Ref<'_, Interner> {
        self.environment.interner.borrow()
    }

    fn newline(&self, out: &mut dyn Write) -> std::io::Result<()> {
        writeln!(out)?;

        for _ in 0..self.indent_levels {
            write!(out, "  ")?;
        }

        Ok(())
    }

    fn borrow_indented(self) -> Self {
        Self {
            indent_levels: self.indent_levels + 1,
            ..self
        }
    }
}

impl<'a> TypingEnvironment {
    pub fn pretty_print(&self) {
        let context = PrettyPrintContext::new(self);

        let mut stdout = std::io::stdout().lock();

        for adt in &self.adts {
            adt.pretty_print(&mut stdout, context).unwrap();
        }

        self.root.pretty_print(&mut stdout, context).unwrap();
        writeln!(stdout).unwrap();
    }

    pub fn pretty_println_val(&'a self, val: &impl PrettyPrint<PrettyPrintContext<'a>>) {
        let context = PrettyPrintContext::new(self);

        let mut stdout = std::io::stdout().lock();

        val.pretty_print(&mut stdout, context).unwrap();

        writeln!(stdout).unwrap();
    }

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
