use crate::parser::ast::term::{Binder, Term};
use crate::parser::atoms::ident::{OwnedPath, Path};
use crate::typeck::level::{Level, LevelArgs};
use crate::typeck::term::{TypedBinder, TypedTerm, TypedTermKind};
use crate::typeck::{TypeError, TypingContext};

impl<'a> TypingContext<'a> {
    pub(super) fn resolve_term(&self, term: &Term) -> Result<TypedTerm, TypeError> {
        match term {
            Term::Sort(u) => Ok(TypedTerm::sort_literal(self.resolve_level(u)?)),
            Term::Path(id, level_args) => {
                self.resolve_path(id.borrow(), &self.resolve_level_args(level_args)?)
            }
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
    fn resolve_path_inner(
        &self,
        path: Path,
        level_args: &LevelArgs,
    ) -> Result<(TypedTerm, usize), TypeError> {
        match self {
            TypingContext::Root(env) => env.resolve_path(path, level_args).map(|t| (t, 0)),
            TypingContext::Binders { binders, parent } => {
                let (first, rest) = path.split_first();

                for (i, binder) in binders.iter().rev().enumerate() {
                    // Check whether the identifier matches the binder
                    if let Some(name) = binder.name {
                        if first == name {
                            // If the identifier resolved to the local variable but there are more segments in the path, give an error
                            if rest.is_some() {
                                return Err(TypeError::LocalVariableIsNotANamespace(
                                    OwnedPath::from_id(first),
                                ));
                            }

                            // Local variables can't have level arguments
                            if level_args.count() != 0 {
                                return Err(TypeError::LevelArgumentGivenForLocalVariable(name));
                            }

                            return Ok((
                                TypedTerm::bound_variable(0, Some(first), binder.ty.clone()),
                                i,
                            ));
                        }
                    }
                }

                // If none of the binders matched, look up the path in the parent context
                parent
                    .resolve_path_inner(path, level_args)
                    .map(|(t, i)| (t, i + binders.len()))
            }
        }
    }

    /// Resolves a path in the current context
    fn resolve_path(&self, path: Path, level_args: &LevelArgs) -> Result<TypedTerm, TypeError> {
        self.resolve_path_inner(path, level_args).map(|(mut t, i)| {
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
        let argument = self.resolve_term(argument)?;

        // Reduce the type of the function
        function.ty.reduce_root();

        // Check that the function has a function type
        let TypedTermKind::PiType { binder, output } = &function.ty else {
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
        let output_ty = output.replace_binder(0, &argument);

        Ok(TypedTerm::make_application(function, argument, output_ty))
    }

    fn resolve_pi_type(&self, binder: &Binder, output: &Term) -> Result<TypedTerm, TypeError> {
        // Resolve the type of the binder, and check that it actually is a type
        let binder_ty = self.resolve_term(&binder.ty)?;
        let binder = TypedBinder {
            name: binder.name,
            ty: binder_ty,
        };

        // Construct a new typing context which includes the new binder
        let c = self.with_binder(&binder);

        // Resolve the output type in this new context
        let output = c.resolve_term(&output)?;

        Ok(TypedTerm::make_pi_type(binder, output))
    }

    fn resolve_lambda(&self, binder: &Binder, body: &Term) -> Result<TypedTerm, TypeError> {
        // Resolve the type of the binder, and check that it actually is a type
        let binder_ty = self.resolve_term(&binder.ty)?;
        let binder = TypedBinder {
            name: binder.name,
            ty: binder_ty,
        };

        // Construct a new typing context which includes the new binder
        let c = self.with_binder(&binder);

        // Resolve the output type in this new context
        let body = c.resolve_term(&body)?;

        Ok(TypedTerm::make_lambda(binder, body))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Interner;
    use crate::parser::ast::item::LevelParameters;
    use crate::parser::atoms::ident::Identifier;
    use crate::typeck::TypingEnvironment;

    #[test]
    fn test_resolve_identifier() {
        let env = TypingEnvironment::new(Interner::new());

        let id_t = Identifier::dummy_val(0);
        let id_x = Identifier::dummy_val(1);

        let context = TypingContext::Root(&env);

        let ty = Level::constant(1);
        let tys = ty.succ();
        let tyss = tys.succ();

        let binder = TypedBinder {
            name: Some(id_t),
            ty: TypedTerm::sort_literal(ty.clone()),
        };
        let context = context.with_binder(&binder);

        let binder = TypedBinder {
            name: Some(id_x),
            ty: TypedTerm::bound_variable(0, Some(id_t), TypedTerm::sort_literal(ty.clone())),
        };
        let context = context.with_binder(&binder);

        assert_eq!(
            context
                .resolve_path(Path::from_id(&id_t), &LevelArgs::default())
                .unwrap(),
            TypedTerm::bound_variable(1, Some(id_t), TypedTerm::sort_literal(ty.clone()))
        );

        assert_eq!(
            context
                .resolve_path(Path::from_id(&id_x), &LevelArgs::default())
                .unwrap(),
            TypedTerm::bound_variable(
                0,
                Some(id_x),
                TypedTerm::bound_variable(1, Some(id_t), TypedTerm::sort_literal(ty.clone()))
            )
        );
    }

    #[test]
    fn test_resolve_path() {
        let mut env = TypingEnvironment::new(Interner::new());

        let id_x = Identifier::dummy_val(0);
        let id_y = Identifier::dummy_val(1);
        let id_z = Identifier::dummy_val(2);
        let id_a = Identifier::dummy_val(3);
        let path_x = OwnedPath::from_id(id_x);
        let path_y = OwnedPath::from_id(id_y);
        let path_z = OwnedPath::from_id(id_z);
        let path_a = OwnedPath::from_id(id_a);

        env.root
            .insert(
                path_x.borrow(),
                LevelParameters::default(),
                TypedTerm::sort_literal(Level::zero()),
            )
            .unwrap();

        let context = TypingContext::Root(&env);

        // The root context should only have id_x, and should check the number of level arguments
        assert_eq!(
            context
                .resolve_path(path_x.borrow(), &LevelArgs::default())
                .unwrap(),
            TypedTerm::sort_literal(Level::zero())
        );
        assert_eq!(
            context
                .resolve_path(path_x.borrow(), &LevelArgs(vec![Level::zero()]))
                .unwrap_err(),
            TypeError::WrongNumberOfLevelArgs {
                path: path_x.clone(),
                expected: 0,
                found: 1,
            }
        );
        assert_eq!(
            context
                .resolve_path(path_y.borrow(), &LevelArgs::default())
                .unwrap_err(),
            TypeError::NameNotResolved(path_y.clone())
        );

        let sort_1 = TypedTerm::sort_literal(Level::constant(1));
        let context = TypingContext::Binders {
            binders: &[
                TypedBinder {
                    name: Some(id_y),
                    ty: sort_1.clone(),
                },
                TypedBinder {
                    name: Some(id_z),
                    ty: TypedTerm::bound_variable(0, Some(id_y), sort_1.clone()),
                },
            ],
            parent: &context,
        };
        // Add another empty context to check that the queries are passed correctly through empty
        // `Binders` contexts
        let context = TypingContext::Binders {
            binders: &[],
            parent: &context,
        };

        // Check that x, y, and z resolve to the correct values
        assert_eq!(
            context
                .resolve_path(path_x.borrow(), &LevelArgs::default())
                .unwrap(),
            TypedTerm::sort_literal(Level::zero())
        );
        assert_eq!(
            context
                .resolve_path(path_y.borrow(), &LevelArgs::default())
                .unwrap(),
            TypedTerm::bound_variable(1, Some(id_y), TypedTerm::sort_literal(Level::constant(1)))
        );
        assert_eq!(
            context
                .resolve_path(path_z.borrow(), &LevelArgs::default())
                .unwrap(),
            TypedTerm::bound_variable(
                0,
                Some(id_z),
                TypedTerm::bound_variable(1, Some(id_y), sort_1.clone())
            )
        );

        // Attempting to give level arguments for a local variable gives an error
        assert_eq!(
            context
                .resolve_path(path_y.borrow(), &LevelArgs(vec![Level::zero()]))
                .unwrap_err(),
            TypeError::LevelArgumentGivenForLocalVariable(id_y),
        );
    }
}
