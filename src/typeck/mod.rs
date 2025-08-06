mod data;
mod error;
mod namespace;
mod term;

pub use error::TypeError;

use crate::parser::ast::Ast;
use crate::parser::ast::item::Item;
use crate::parser::ast::item::data::DataDefinition;
use crate::parser::ast::item::def::ValueDefinition;
use crate::parser::ast::term::{Binder, Term, Universe};
use crate::parser::atoms::{Identifier, OwnedPath, Path};
use crate::parser::{Interner, PrettyPrint};
use crate::typeck::data::{Adt, AdtConstructor, AdtConstructorParam, AdtConstructorParamKind};
use crate::typeck::namespace::Namespace;
use crate::typeck::term::{TypedBinder, TypedTerm, TypedTermKind};
use std::io::Write;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct AdtIndex(usize);

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
            root: Namespace::new(),
        }
    }

    fn get_adt(&self, id: AdtIndex) -> &Adt {
        &self.adts[id.0]
    }

    fn resolve_path(&self, path: Path) -> Result<TypedTerm, TypeError> {
        self.root.resolve(path)
    }

    pub fn resolve_file(&mut self, ast: &Ast) -> Result<(), TypeError> {
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

    fn resolve_data_definition(&mut self, ast: &DataDefinition) -> Result<(), TypeError> {
        let family = TypingContext::Root(self).resolve_term(&ast.family)?;

        let Ok(family_univ) = family.check_is_ty() else {
            return Err(TypeError::NotASortFamily(family));
        };

        // Resolve the type's family as a telescope
        let (indices, out) = family.clone().into_telescope();
        // Check that the output of the telescope is a sort
        let Ok(sort) = out.term.check_is_sort() else {
            return Err(TypeError::NotASortFamily(family));
        };

        let adt_index = AdtIndex(self.adts.len());

        // Add the ADT so that the constructors can refer to it. The actual constructors will be added to this definition later.
        self.adts.push(Adt {
            name: ast.name.clone(),
            indices,
            sort,
            constructors: vec![],
        });
        self.root.insert(
            ast.name.borrow(),
            TypedTerm {
                universe: family_univ,
                ty: family.term,
                term: TypedTermKind::AdtName(adt_index),
            },
        )?;
        self.root.insert_namespace(ast.name.borrow());

        self.resolve_adt_constructors(&ast, adt_index)?;

        Ok(())
    }

    fn resolve_adt_constructors(
        &mut self,
        ast: &&DataDefinition,
        adt_index: AdtIndex,
    ) -> Result<(), TypeError> {
        let mut constructor_tys = Vec::new();
        for constructor in &ast.constructors {
            let ty = TypingContext::Root(self).resolve_term(&constructor.telescope)?;
            let universe = ty.check_is_ty()?;
            constructor_tys.push((constructor.name, ty, universe));
        }

        let mut constructors = Vec::new();

        for (i, (name, ty, universe)) in constructor_tys.into_iter().enumerate() {
            let constructor = self.resolve_adt_constructor(name, &ty, adt_index)?;

            constructors.push(constructor);

            let adt_namespace = self.root.resolve_namespace_mut(ast.name.borrow())?;
            adt_namespace.insert(
                Path::from_id(&name),
                TypedTerm {
                    universe,
                    ty: ty.term,
                    term: TypedTermKind::AdtConstructor(adt_index, i),
                },
            )?;
        }

        // TODO: generate eliminators

        self.adts.last_mut().unwrap().constructors = constructors;


        Ok(())
    }

    fn resolve_adt_constructor(
        &self,
        name: Identifier,
        ty: &TypedTerm,
        adt_index: AdtIndex,
    ) -> Result<AdtConstructor, TypeError> {
        // Check that the constructor is actually a type, and decompose it as a telescope
        ty.check_is_ty()?;
        let (params, result) = ty.clone().into_telescope();

        let mut processed_params = Vec::new();
        for param in params {
            processed_params.push(self.resolve_adt_constructor_param(name, adt_index, param)?);
        }

        // Decompose the output of the telescope as a series of applications.
        // The underlying function should be the name of the ADT being constructed
        let (f, arguments) = result.into_application_stack();

        // Check that the underlying function is the correct ADT name
        match f.term {
            TypedTermKind::AdtName(id) if id == adt_index => (),

            _ => {
                return Err(TypeError::IncorrectConstructorResultantType {
                    name,
                    found: f,
                    expected: adt_index,
                });
            }
        }

        for argument in &arguments {
            // TODO: check that argument does not include references to the current ADT
        }

        Ok(AdtConstructor {
            name,
            ty: ty.term.clone(),
            params: processed_params,
            indices: arguments,
        })
    }

    fn resolve_adt_constructor_param(
        &self,
        name: Identifier,
        adt_index: AdtIndex,
        param: TypedBinder,
    ) -> Result<AdtConstructorParam, TypeError> {
        let (parameters, output) = param.ty.clone().into_telescope();
        let (f, args) = output.into_application_stack();

        // If f is the ADT being constructed, then this is an inductive parameter
        let param_kind = match f.term {
            TypedTermKind::AdtName(id) if id == adt_index => {
                for binder in &parameters {
                    binder.ty.term.forbid_references_to_adt(adt_index)?;
                }
                for arg in &args {
                    arg.term.forbid_references_to_adt(adt_index)?;
                }

                AdtConstructorParamKind::Inductive {
                    parameters,
                    indices: args,
                }
            }

            // If the type has any other form, then just check that it doesn't contain the ADT at all
            _ => {
                param.ty.term.forbid_references_to_adt(adt_index)?;

                AdtConstructorParamKind::NonInductive(param.ty)
            }
        };

        Ok(AdtConstructorParam {
            name: Some(name),
            kind: param_kind,
        })
    }

    fn resolve_value_definition(&mut self, ast: &ValueDefinition) -> Result<(), TypeError> {
        let mut ty = ast.ty.clone();
        let mut value = ast.value.clone();

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

        self.root.insert(ast.path.borrow(), value)?;

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

    fn resolve_term(&self, term: &Term) -> Result<TypedTerm, TypeError> {
        match term {
            Term::SortLiteral(u) => Ok(TypedTerm {
                universe: u.succ().succ(),
                ty: TypedTermKind::SortLiteral(u.succ()),
                term: TypedTermKind::SortLiteral(*u),
            }),
            Term::Path(id) => self.resolve_path(id.borrow()),
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
    fn resolve_path_inner(&self, path: Path) -> Result<(TypedTerm, usize), TypeError> {
        match self {
            TypingContext::Root(env) => env.resolve_path(path).map(|t| (t, 0)),
            TypingContext::Binder { binder, parent } => {
                let (first, rest) = path.split_first();

                if let Some(name) = binder.name {
                    if first == name {
                        if rest.is_some() {
                            return Err(TypeError::NotANamespace(OwnedPath::from_id(first)));
                        }

                        return Ok((
                            TypedTerm {
                                universe: binder.ty.universe.pred(),
                                ty: binder.ty.term.clone(),
                                term: TypedTermKind::BoundVariable {
                                    index: 0,
                                    name: first,
                                },
                            },
                            0,
                        ));
                    }
                }

                parent.resolve_path_inner(path).map(|(t, i)| (t, i + 1))
            }
        }
    }

    /// Resolves a path in the current context
    fn resolve_path(&self, path: Path) -> Result<TypedTerm, TypeError> {
        self.resolve_path_inner(path).map(|(mut t, i)| {
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
            universe: output.universe,
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

        // Calculate the universe of the new type
        let univ = binder_univ.max(output_univ); // TODO: special rules for Prop

        Ok(TypedTerm {
            universe: univ.succ(),
            ty: TypedTermKind::SortLiteral(univ),
            term: TypedTermKind::PiType {
                binder: Box::new(binder),
                output: Box::new(output),
            },
        })
    }

    fn resolve_lambda(&self, binder: &Binder, body: &Term) -> Result<TypedTerm, TypeError> {
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
        let body = c.resolve_term(&body)?;

        // Calculate the universe of the new term
        let univ = binder_univ.max(body.universe); // TODO: special rules for Prop

        Ok(TypedTerm {
            universe: univ,
            ty: TypedTermKind::PiType {
                binder: Box::new(binder.clone()),
                output: Box::new(TypedTerm {
                    universe: body.universe.succ(),
                    ty: TypedTermKind::SortLiteral(body.universe),
                    term: body.ty.clone(),
                }),
            },
            term: TypedTermKind::Lambda {
                binder: Box::new(binder),
                body: Box::new(body),
            },
        })
    }
}

#[derive(Debug, Copy, Clone)]
struct PrettyPrintContext<'a> {
    environment: &'a TypingEnvironment<'a>,
}

impl<'a> PrettyPrintContext<'a> {
    fn interner(&self) -> &Interner {
        self.environment.interner
    }
}

impl<'a> TypingEnvironment<'a> {
    pub fn pretty_print(&self) {
        let context = PrettyPrintContext { environment: self };

        let mut stdout = std::io::stdout().lock();

        for adt in &self.adts {
            adt.pretty_print(&mut stdout, context).unwrap();
        }

        self.root.pretty_print(&mut stdout, context).unwrap();
    }

    pub fn pretty_print_val(&'a self, val: &impl PrettyPrint<PrettyPrintContext<'a>>) {
        let context = PrettyPrintContext { environment: self };

        let mut stdout = std::io::stdout().lock();

        val.pretty_print(&mut stdout, context).unwrap();
    }

    pub fn pretty_println_val(&'a self, val: &impl PrettyPrint<PrettyPrintContext<'a>>) {
        let context = PrettyPrintContext { environment: self };

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
        self.sort.pretty_print(out, ())?;

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
    use super::*;

    #[test]
    fn test_resolve_identifier() {
        let env = TypingEnvironment {
            interner: &Interner::new(),
            adts: vec![],
            root: Namespace::new(),
        };

        let id_t = Identifier::dummy_val(0);
        let id_x = Identifier::dummy_val(1);

        let context = TypingContext::Root(&env);

        let context = TypingContext::Binder {
            binder: &TypedBinder {
                name: Some(id_t),
                ty: TypedTerm {
                    universe: Universe::TYPE.succ().succ(),
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
                    universe: Universe::TYPE.succ(),
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
            context.resolve_path(Path::from_id(&id_t)).unwrap(),
            TypedTerm {
                universe: Universe::TYPE.succ(),
                ty: TypedTermKind::SortLiteral(Universe::TYPE),
                term: TypedTermKind::BoundVariable {
                    index: 1,
                    name: id_t
                },
            },
        );

        assert_eq!(
            context.resolve_path(Path::from_id(&id_x)).unwrap(),
            TypedTerm {
                universe: Universe::TYPE,
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
