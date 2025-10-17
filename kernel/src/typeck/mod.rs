mod context;
mod data;
mod error;
mod level;
mod namespace;
mod term;

pub use error::TypeError;

use std::cell::{Ref, RefCell};

use crate::diagnostic::KernelDiagnostic;
use crate::typeck::data::Adt;
use crate::typeck::level::LevelArgs;
use crate::typeck::namespace::Namespace;
use crate::typeck::term::{Abbreviation, TypedBinder, TypedTerm};
use common::{Interner, PrettyPrint, WithDiagnostics};
use std::io::Write;
use parser::ast::item::{Item, LevelParameters};
use parser::ast::{parse_file, Ast};
use parser::ast::item::axiom::AxiomDefinition;
use parser::ast::item::def::ValueDefinition;
use parser::ast::term::Term;
use parser::atoms::ident::{OwnedPath, Path};

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct AdtIndex(usize);

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct AxiomIndex(usize);

#[derive(Debug)]
pub struct TypingEnvironment {
    interner: RefCell<Interner>,
    adts: Vec<Adt>,
    root: Namespace,
    /// The paths to all defined axioms
    axioms: Vec<Axiom>,
    /// The level parameters of the item currently being type checked
    level_parameters: Option<LevelParameters>,
}

#[derive(Debug)]
pub struct Axiom {
    index: AxiomIndex,
    path: OwnedPath,
    level_params: LevelParameters,
    ty: TypedTerm,
}

impl TypingEnvironment {
    pub fn from_str(source: &str) -> WithDiagnostics<Self, KernelDiagnostic> {
        parse_file(source)
            .map_diagnostics(KernelDiagnostic::Parse)
            .flat_map(|(interner, ast)| {
                let mut env = Self::new(interner);
                env.resolve_file(&ast)
                    .map_diagnostics(KernelDiagnostic::Type)
                    .with_value(env)
            })
    }

    pub fn new(interner: Interner) -> Self {
        Self {
            interner: RefCell::new(interner),
            adts: vec![],
            root: Namespace::new(),
            axioms: vec![],
            level_parameters: None,
        }
    }

    fn get_adt(&self, id: AdtIndex) -> &Adt {
        &self.adts[id.0]
    }

    fn get_axiom(&self, id: AxiomIndex) -> &Axiom {
        &self.axioms[id.0]
    }

    fn resolve_path(&self, path: Path, level_args: &LevelArgs) -> Result<TypedTerm, TypeError> {
        self.root.resolve(path, level_args)
    }

    pub fn resolve_file(&mut self, ast: &Ast) -> WithDiagnostics<(), TypeError> {
        let mut res = WithDiagnostics::new(());

        for item in &ast.items {
            // TODO: convert these methods to use WithDiagnostics themselves
            match item {
                Item::DataDefinition(dd) => {
                    self.resolve_adt(dd).unwrap_or_else(|e| res.push_error(e));
                }
                Item::ValueDefinition(vd) => {
                    self.resolve_value_definition(vd)
                        .unwrap_or_else(|e| res.push_error(e));
                }
                Item::Axiom(ad) => self
                    .resolve_axiom_definition(ad)
                    .unwrap_or_else(|e| res.push_error(e)),
            }
        }

        res
    }

    fn resolve_value_definition(&mut self, ast: &ValueDefinition) -> Result<(), TypeError> {
        let mut ty = ast.ty.clone();
        let mut value = ast.value.clone();

        // Set the level parameters for this item
        self.set_level_params(ast.level_params.clone())?;

        // Desugar `def` parameters to pi types and lambda expressions
        for binder in ast.binders.iter().rev() {
            ty = Term::PiType {
                binder: Box::new(binder.clone()),
                output: Box::new(ty),
            };

            value = Term::Lambda {
                binder: Box::new(binder.clone()),
                body: Box::new(value),
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

        let term =
            TypedTerm::value_of_type(value.term(), ty).with_abbreviation(Abbreviation::Constant(
                ast.path.clone(),
                LevelArgs::from_level_parameters(&ast.level_params),
            ));

        #[cfg(debug_assertions)]
        self.check_term(term.clone());

        self.root
            .insert(ast.path.borrow(), ast.level_params.clone(), term)?;

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
            ty = Term::PiType {
                binder: Box::new(binder.clone()),
                output: Box::new(ty),
            };
        }

        // Resolve the type of the axiom
        let ty = TypingContext::Root(self).resolve_term(&ty)?;

        let axiom = self.add_axiom(ast.path.clone(), ast.level_params.clone(), ty.clone());

        let term = TypedTerm::axiom(
            axiom.index,
            ty,
            LevelArgs::from_level_parameters(&ast.level_params),
        );

        self.root
            .insert(ast.path.borrow(), ast.level_params.clone(), term)?;

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
    fn new(environment: &'a TypingEnvironment) -> Self {
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

#[cfg(test)]
mod tests {
    use parser::ast::parse_file;
    use parser::ast::tests::parse_term;
    use crate::typeck::term::TypedTerm;
    use crate::typeck::{TypeError, TypingContext, TypingEnvironment};

    pub fn assert_type_checks(source: &str) {
        let (interner, ast) = parse_file(source).unwrap();
        let mut env = TypingEnvironment::new(interner);

        env.resolve_file(&ast)
            .expect("Code should have type checked");
    }

    pub fn assert_type_error(source: &str, errors: &[TypeError]) {
        let (interner, ast) = parse_file(source).unwrap();
        let mut env = TypingEnvironment::new(interner);

        let res = env.resolve_file(&ast);

        if !res
            .diagnostics
            .iter()
            .map(|d| &d.value)
            .eq(errors.into_iter())
        {
            panic!(
                "Type errors were wrong.\nExpected: {errors:?}\nFound: {:?}",
                res.diagnostics
            );
        }
    }


    impl TypingEnvironment {
        pub fn resolve_term_from_string(&mut self, term: &str) -> TypedTerm {
            let term = parse_term(&mut self.interner.borrow_mut(), term).unwrap();
            TypingContext::Root(self).resolve_term(&term).unwrap()
        }
    }
}
