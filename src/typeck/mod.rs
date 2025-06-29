mod error;
mod term;

pub use error::TypeError;

use crate::parser::ast::Ast;
use crate::parser::ast::item::Item;
use crate::parser::ast::item::data::DataDefinition;
use crate::parser::ast::term::{Binder, Term, Universe};
use crate::parser::atoms::Identifier;
use crate::parser::{Interner, PrettyPrint};
use crate::typeck::term::{TypedBinder, TypedTerm, TypedTermKind};
use std::collections::HashMap;
use std::io::Write;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct AdtIndex(usize);

#[derive(Debug)]
pub struct Adt {
    name: Identifier,
    family: TypedTerm,
    constructors: Vec<AdtConstructor>,
}

#[derive(Debug)]
pub struct AdtConstructor {
    name: Identifier,
    ty: TypedTerm,
}

#[derive(Debug)]
pub struct TypingEnvironment<'a> {
    interner: &'a Interner,
    adts: Vec<Adt>,
    root: Namespace,
}

impl<'a> TypingEnvironment<'a> {
    pub fn new(interner: &'a Interner) -> Self {
        Self {
            interner,
            adts: vec![],
            root: Namespace {
                values: Default::default(),
            },
        }
    }

    fn get_adt(&self, id: AdtIndex) -> &Adt {
        &self.adts[id.0]
    }

    fn resolve_identifier(&self, id: Identifier) -> Result<TypedTerm, TypeError> {
        self.root.resolve_identifier(id)
    }

    pub fn resolve_file(&mut self, ast: &Ast) -> Result<(), TypeError> {
        for item in &ast.items {
            match item {
                Item::DataDefinition(dd) => {
                    self.resolve_data_definition(dd)?;
                }
                Item::Class => {}
                Item::Instance => {}
                Item::Def => {}
            }
        }

        Ok(())
    }

    fn resolve_data_definition(&mut self, ast: &DataDefinition) -> Result<(), TypeError> {
        let family = TypingContext::Root(self).resolve_term(&ast.family)?;

        // TODO: check that `family` is a valid family of sorts

        let adt_index = AdtIndex(self.adts.len());

        self.adts.push(Adt {
            name: ast.name,
            family: family.clone(),
            constructors: vec![],
        });

        self.root.values.insert(
            ast.name,
            TypedTerm {
                ty: family.clone().term,
                term: TypedTermKind::AdtName(adt_index),
            },
        );

        let mut constructors = Vec::new();
        for constructor in &ast.constructors {
            let ty = TypingContext::Root(self).resolve_term(&constructor.telescope)?;
            ty.check_is_ty()?;
            constructors.push(AdtConstructor {
                name: constructor.name,
                ty,
            });
        }

        for (i, constructor) in constructors.iter().enumerate() {
            self.root.values.insert(
                constructor.name,
                TypedTerm {
                    ty: constructor.ty.term.clone(),
                    term: TypedTermKind::AdtConstructor(adt_index, i),
                },
            );
        }

        // TODO: check that the constructors actually end in a member of the type
        // TODO: positivity checking

        self.adts.last_mut().unwrap().constructors = constructors;

        Ok(())
    }
}

#[derive(Debug)]
struct Namespace {
    values: HashMap<Identifier, TypedTerm>,
}

impl Namespace {
    fn resolve_identifier(&self, id: Identifier) -> Result<TypedTerm, TypeError> {
        self.values
            .get(&id)
            .cloned()
            .ok_or(TypeError::NameNotResolved(id))
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

    fn resolve_term(&self, term: &Term) -> Result<TypedTerm, TypeError> {
        match term {
            Term::SortLiteral(u) => Ok(TypedTerm {
                // universe: u.succ().succ(),
                ty: TypedTermKind::SortLiteral(u.succ()),
                term: TypedTermKind::SortLiteral(*u),
            }),
            Term::Identifier(id) => self.resolve_identifier(*id),
            Term::Application { function, argument } => {
                self.resolve_application(function, argument)
            }
            Term::PiType { binder, output } => self.resolve_pi_type(binder, output),
            Term::Lambda { binder, body } => self.resolve_lambda(binder, body),
        }
    }

    /// Resolves an identifier in the context. On success, returns the associated term as well as the number of 
    /// binders between that binder's introduction and the current context - the binders in the term need to be
    /// increased by this number, which is done in [`resolve_identifier`][Self::resolve_identifier]
    fn resolve_identifier_inner(&self, id: Identifier) -> Result<(TypedTerm, usize), TypeError> {
        match self {
            TypingContext::Root(env) => env.resolve_identifier(id).map(|t| (t, 0)),
            TypingContext::Binder { binder, parent } => {
                if let Some(name) = binder.name {
                    if id == name {
                        return Ok((
                            TypedTerm {
                                ty: binder.ty.term.clone(),
                                term: TypedTermKind::BoundVariable { index: 0, name: id },
                            },
                            0,
                        ));
                    }
                }

                parent.resolve_identifier_inner(id).map(|(t, i)|(t, i + 1))
            }
        }
    }

    /// Resolves an identifier in the current context
    fn resolve_identifier(&self, id: Identifier) -> Result<TypedTerm, TypeError> {
        self.resolve_identifier_inner(id).map(|(mut t, i)| {
            // The term includes its own binder while the type doesn't, so the type needs to be incremented by one more than the term
            t.ty.increment_binders_above(0, i + 1);
            t.term.increment_binders_above(0, i);
            t
        })
    }

    fn resolve_application(
        &self,
        function: &Term,
        argument: &Term,
    ) -> Result<TypedTerm, TypeError> {
        // Type check the function and argument
        let mut function = self.resolve_term(function)?;
        let mut argument = self.resolve_term(argument)?;

        // Reduce the type of the function
        function.ty.reduce_root();

        // println!("Function and argument:");
        // self.environment().pretty_println_val(&function.term);
        // self.environment().pretty_println_val(&function.ty);
        // self.environment().pretty_println_val(&argument.term);
        // self.environment().pretty_println_val(&argument.ty);
        // println!();

        // Check that the function has a function type
        let TypedTermKind::PiType { binder, output } = &mut function.ty else {
            return Err(TypeError::NotAFunction(function));
        };

        // Check that the type of the argument matches the input type of the function
        // TODO: do this check without cloning
        if !binder.ty.term.clone().def_eq(argument.ty.clone()) {
            return Err(TypeError::MismatchedTypes {
                term: argument,
                expected: binder.ty.clone(),
            });
        }

        // Replace instances of the binder in the output type with the argument
        let output_ty = output.term.replace_binder(0, &argument);

        Ok(TypedTerm {
            ty: output_ty,
            term: TypedTermKind::Application {
                function: Box::new(function),
                argument: Box::new(argument),
            },
        })
    }

    fn resolve_pi_type(&self, binder: &Binder, output: &Term) -> Result<TypedTerm, TypeError> {
        // Resolve the type of the binder, and check that it actually is a type
        let binder_ty = self.resolve_term(&binder.ty)?;
        let binder_univ = binder_ty.check_is_ty()?;
        let binder = TypedBinder {
            name: binder.name,
            ty: binder_ty,
        };

        // Construct a new typing context which includes the new binder
        let c = TypingContext::Binder {
            binder: &binder,
            parent: self,
        };

        // Resolve the output type in this new context
        let output = c.resolve_term(&output)?;
        let output_univ = output.check_is_ty()?;

        Ok(TypedTerm {
            ty: TypedTermKind::SortLiteral(binder_univ.max(output_univ)), // TODO: special rules for Prop
            term: TypedTermKind::PiType {
                binder: Box::new(binder),
                output: Box::new(output),
            },
        })
    }

    fn resolve_lambda(&self, binder: &Binder, body: &Term) -> Result<TypedTerm, TypeError> {
        todo!()
    }
}

#[derive(Debug, Copy, Clone)]
struct PrettyPrintContext<'a> {
    environment: &'a TypingEnvironment<'a>,
    binders: usize,
}

impl<'a> PrettyPrintContext<'a> {
    fn interner(&self) -> &Interner {
        self.environment.interner
    }
}

impl<'a> TypingEnvironment<'a> {
    pub fn pretty_print(&self) {
        let context = PrettyPrintContext {
            environment: self,
            binders: 0,
        };

        let mut stdout = std::io::stdout().lock();

        for adt in &self.adts {
            adt.pretty_print(&mut stdout, context).unwrap();
        }

        self.root.pretty_print(&mut stdout, context).unwrap();
    }

    pub fn pretty_print_val(&'a self, val: &impl PrettyPrint<PrettyPrintContext<'a>>) {
        let context = PrettyPrintContext {
            environment: self,
            binders: 0,
        };

        let mut stdout = std::io::stdout().lock();

        val.pretty_print(&mut stdout, context).unwrap();
    }

    pub fn pretty_println_val(&'a self, val: &impl PrettyPrint<PrettyPrintContext<'a>>) {
        let context = PrettyPrintContext {
            environment: self,
            binders: 0,
        };

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
        self.family.term.pretty_print(out, context)?;
        writeln!(out, " where")?;

        for constructor in &self.constructors {
            write!(out, "  ")?;
            constructor.name.pretty_print(out, context.interner())?;
            write!(out, " : ")?;
            constructor.ty.term.pretty_print(out, context)?;
            writeln!(out)?;
        }

        writeln!(out)
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_resolve_identifier() {
        let env = TypingEnvironment {
            interner: &Interner::new(),
            adts: vec![],
            root: Namespace {
                values: Default::default(),
            },
        };

        let id_t = Identifier::dummy_val(0);
        let id_x = Identifier::dummy_val(1);

        let context = TypingContext::Root(&env);

        let context = TypingContext::Binder {
            binder: &TypedBinder {
                name: Some(id_t),
                ty: TypedTerm {
                    ty: TypedTermKind::SortLiteral(Universe::TYPE.succ()),
                    term: TypedTermKind::SortLiteral(Universe::TYPE),
                },
            },
            parent: &context,
        };

        let context = TypingContext::Binder {
            binder: &TypedBinder {
                name: Some(id_x),
                ty: TypedTerm {
                    ty: TypedTermKind::SortLiteral(Universe::TYPE),
                    term: TypedTermKind::BoundVariable {
                        index: 0,
                        name: id_t,
                    },
                },
            },
            parent: &context,
        };

        assert_eq!(
            context.resolve_identifier(id_t).unwrap(),
            TypedTerm {
                ty: TypedTermKind::SortLiteral(Universe::TYPE),
                term: TypedTermKind::BoundVariable {
                    index: 1,
                    name: id_t
                },
            },
        );

        assert_eq!(
            context.resolve_identifier(id_x).unwrap(),
            TypedTerm {
                ty: TypedTermKind::BoundVariable {
                    index: 1,
                    name: id_t
                },
                term: TypedTermKind::BoundVariable {
                    index: 0,
                    name: id_x
                },
            },
        );
    }
}
