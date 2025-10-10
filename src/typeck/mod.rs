mod context;
mod data;
mod error;
mod level;
mod namespace;
mod term;

pub use error::TypeError;

use std::cell::{Ref, RefCell};

use crate::parser::ast::Ast;
use crate::parser::ast::item::def::ValueDefinition;
use crate::parser::ast::item::{Item, LevelParameters};
use crate::parser::ast::term::Term;
use crate::parser::atoms::ident::{Identifier, Path};
use crate::parser::{Interner, PrettyPrint};
use crate::typeck::data::Adt;
use crate::typeck::level::LevelArgs;
use crate::typeck::namespace::Namespace;
use crate::typeck::term::{TypedBinder, TypedTerm};
use std::io::Write;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct AdtIndex(usize);

#[derive(Debug)]
pub struct TypingEnvironment {
    interner: RefCell<Interner>,
    adts: Vec<Adt>,
    root: Namespace,
    /// The level parameters of the item currently being type checked
    level_parameters: Option<LevelParameters>,
}

impl TypingEnvironment {
    pub fn new(interner: Interner) -> Self {
        Self {
            interner: RefCell::new(interner),
            adts: vec![],
            root: Namespace::new(),
            level_parameters: None,
        }
    }

    fn get_adt(&self, id: AdtIndex) -> &Adt {
        &self.adts[id.0]
    }

    fn resolve_path(&self, path: Path, level_args: &LevelArgs) -> Result<TypedTerm, TypeError> {
        self.root.resolve(path, level_args)
    }

    pub fn resolve_file(&mut self, ast: &Ast) -> Result<(), TypeError> {
        for item in &ast.items {
            match item {
                Item::DataDefinition(dd) => {
                    self.resolve_adt(dd)?;
                }
                Item::Class => {}
                Item::Instance => {}
                Item::ValueDefinition(vd) => {
                    self.resolve_value_definition(vd)?;
                }
            }
        }

        Ok(())
    }

    fn assemble_telescope(
        params: Vec<(Option<Identifier>, TypedTerm)>,
        output: TypedTerm,
    ) -> Result<TypedTerm, TypeError> {
        params
            .into_iter()
            .rev()
            .try_fold(output, |out, (name, param)| {
                Ok(TypedTerm::make_pi_type(
                    TypedBinder { name, ty: param },
                    out,
                ))
            })
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

        self.root.insert(
            ast.path.borrow(),
            ast.level_params.clone(),
            TypedTerm::value_of_type(value.term(), ty),
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

    fn get_binder(&self, index: usize) -> Option<&'a TypedBinder> {
        match self {
            TypingContext::Root(_) => None,
            TypingContext::Binders { binders, parent } => {
                if index < binders.len() {
                    // Outer binders are before inner ones in this list,
                    // so binder 0 is the last one, 1 is the second last, etc.
                    Some(&binders[binders.len() - index - 1])
                } else {
                    parent.get_binder(index - binders.len())
                }
            }
        }
    }
}

#[derive(Debug, Copy, Clone)]
struct PrettyPrintContext<'a> {
    environment: &'a TypingEnvironment,
    indent_levels: usize,
}

impl<'a> PrettyPrintContext<'a> {
    fn new(environment: &'a TypingEnvironment) -> Self {
        Self {
            environment,
            indent_levels: 0,
        }
    }

    fn interner(&self) -> Ref<Interner> {
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

    pub fn pretty_print_val(&'a self, val: &impl PrettyPrint<PrettyPrintContext<'a>>) {
        let context = PrettyPrintContext::new(self);

        let mut stdout = std::io::stdout().lock();

        val.pretty_print(&mut stdout, context).unwrap();
    }

    pub fn pretty_println_val(&'a self, val: &impl PrettyPrint<PrettyPrintContext<'a>>) {
        let context = PrettyPrintContext::new(self);

        let mut stdout = std::io::stdout().lock();

        val.pretty_print(&mut stdout, context).unwrap();

        writeln!(stdout).unwrap();
    }
}

#[cfg(test)]
mod tests {
    use crate::parser::ast::tests::parse_term;
    use crate::typeck::term::TypedTerm;
    use crate::typeck::{TypingContext, TypingEnvironment};

    macro_rules! assert_type_checks {
        ($source: expr) => {{
            let (interner, ast) = $crate::parser::ast::parse_file($source).unwrap();
            let mut env = $crate::typeck::TypingEnvironment::new(interner);

            env.resolve_file(&ast)
                .expect("Code should have type checked");
        }};
    }
    pub(in crate::typeck) use assert_type_checks;

    macro_rules! assert_type_error {
        ($source: expr, $error: expr) => {{
            let (interner, ast) = $crate::parser::ast::parse_file($source).unwrap();
            let mut env = $crate::typeck::TypingEnvironment::new(interner);

            let err = env
                .resolve_file(&ast)
                .expect_err("Code should have failed to type check");

            assert_eq!(err, $error);
        }};
    }

    pub(in crate::typeck) use assert_type_error;

    impl TypingEnvironment {
        pub fn resolve_term_from_string(&mut self, term: &str) -> TypedTerm {
            let term = parse_term(&mut self.interner.borrow_mut(), term).unwrap();
            TypingContext::Root(self).resolve_term(&term).unwrap()
        }
    }
}
