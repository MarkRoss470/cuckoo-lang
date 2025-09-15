mod data;
mod error;
mod level;
mod namespace;
mod term;

pub use error::TypeError;

use crate::parser::ast::Ast;
use crate::parser::ast::item::def::ValueDefinition;
use crate::parser::ast::item::{Item, LevelParameters};
use crate::parser::ast::term::Term;
use crate::parser::atoms::ident::{Identifier, Path};
use crate::parser::{Interner, PrettyPrint};
use crate::typeck::data::Adt;
use crate::typeck::level::LevelArgs;
use crate::typeck::namespace::Namespace;
use crate::typeck::term::{TypedBinder, TypedTerm, TypedTermKind};
use std::io::Write;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct AdtIndex(usize);

#[derive(Debug)]
pub struct TypingEnvironment<'a> {
    ast: &'a Ast,
    adts: Vec<Adt>,
    root: Namespace,
    /// The level parameters of the item currently being type checked
    level_parameters: Option<&'a LevelParameters>,
}

impl<'a> TypingEnvironment<'a> {
    pub fn new(ast: &'a Ast) -> Self {
        Self {
            ast,
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

    pub fn resolve_file(&mut self, ast: &'a Ast) -> Result<(), TypeError> {
        for item in &ast.items {
            match item {
                Item::DataDefinition(dd) => {
                    self.resolve_data_definition(dd)?;
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
                let param_level = param.check_is_ty()?;
                let output_level = out.check_is_ty()?;

                let pi_level = param_level.smart_max(&output_level);

                Ok(TypedTerm {
                    level: pi_level.succ(),
                    ty: TypedTermKind::SortLiteral(pi_level),
                    term: TypedTermKind::PiType {
                        binder: Box::new(TypedBinder { name, ty: param }),
                        output: Box::new(out),
                    },
                })
            })
    }

    fn resolve_value_definition(&mut self, ast: &'a ValueDefinition) -> Result<(), TypeError> {
        let mut ty = ast.ty.clone();
        let mut value = ast.value.clone();

        // Set the level parameters for this item
        self.set_level_params(&ast.level_params)?;

        // TODO: validate level parameters (do this for def statements too)

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
        ty.check_is_ty()?;

        // Resolve the value of the `def`
        let value = TypingContext::Root(self).resolve_term(&value)?;

        // TODO: do this check without cloning
        if !ty.term.clone().def_eq(value.ty.clone()) {
            return Err(TypeError::MismatchedTypes {
                term: value,
                expected: ty,
            });
        }

        self.root
            .insert(ast.path.borrow(), ast.level_params.clone(), value)?;

        // Remove the level parameters from the context
        self.clear_level_params();

        Ok(())
    }
}

#[derive(Debug, Copy, Clone)]
enum TypingContext<'a> {
    Root(&'a TypingEnvironment<'a>),
    Binder {
        binder: &'a TypedBinder,
        parent: &'a TypingContext<'a>,
    },
}

impl<'a> TypingContext<'a> {
    fn environment(&self) -> &TypingEnvironment {
        match self {
            TypingContext::Root(env) => env,
            TypingContext::Binder { binder: _, parent } => parent.environment(),
        }
    }

    fn get_binder(&self, index: usize) -> Option<&'a TypedBinder> {
        match self {
            TypingContext::Root(_) => None,
            TypingContext::Binder { binder, parent } => {
                if index == 0 {
                    Some(binder)
                } else {
                    parent.get_binder(index - 1)
                }
            }
        }
    }
}

#[derive(Debug, Copy, Clone)]
struct PrettyPrintContext<'a> {
    environment: &'a TypingEnvironment<'a>,
    indent_levels: usize,
}

impl<'a> PrettyPrintContext<'a> {
    fn new(environment: &'a TypingEnvironment<'a>) -> Self {
        Self {
            environment,
            indent_levels: 0,
        }
    }

    fn interner(&self) -> &Interner {
        &self.environment.ast.interner
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

impl<'a> TypingEnvironment<'a> {
    pub fn pretty_print(&self) {
        let context = PrettyPrintContext::new(self);

        let mut stdout = std::io::stdout().lock();

        for adt in &self.adts {
            adt.pretty_print(&mut stdout, context).unwrap();
        }

        self.root.pretty_print(&mut stdout, context).unwrap();
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

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for Adt {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext<'a>,
    ) -> std::io::Result<()> {
        write!(out, "data ")?;
        self.name.pretty_print(out, context.interner())?;
        write!(out, " : ")?;

        for index in &self.indices {
            index.pretty_print(out, context)?;
            write!(out, " -> ")?;
        }
        self.sort.pretty_print(out, context)?;

        writeln!(out, " where")?;

        for constructor in &self.constructors {
            write!(out, "  ")?;
            constructor.name.pretty_print(out, context.interner())?;
            write!(out, " : ")?;
            constructor.ty.pretty_print(out, context)?;
            writeln!(out)?;
        }

        writeln!(out)
    }
}

#[cfg(test)]
mod tests {
    macro_rules! setup_env {
        ($env: ident) => {
            let ast = $crate::parser::ast::Ast {
                interner: $crate::parser::Interner::new(),
                items: Vec::new(),
            };

            #[allow(unused_mut)]
            let mut $env = $crate::typeck::TypingEnvironment::new(&ast);
        };
    }

    pub(in crate::typeck) use setup_env;
}
