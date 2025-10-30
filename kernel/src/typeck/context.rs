use crate::typeck::error::TypeErrorKind;
use crate::typeck::level::LevelArgs;
use crate::typeck::term::{TypedBinder, TypedTerm};
use crate::typeck::{TypeError, TypingContext};
use parser::ast::term::{Binder, Term, TermKind};
use parser::atoms::ident::{OwnedPath, Path};
use parser::error::Span;

impl<'a> TypingContext<'a> {
    pub(super) fn resolve_term(&self, term: &Term) -> Result<TypedTerm, TypeError> {
        let span = term.span.clone();

        match &term.kind {
            TermKind::Sort(u) => Ok(TypedTerm::sort_literal(self.resolve_level(u)?, span)),
            TermKind::Path(id, level_args) => self.resolve_path(
                id.borrow(),
                &self.resolve_level_args(level_args.clone())?,
                span,
            ),
            TermKind::Application { function, argument } => {
                self.resolve_application(function, argument, span)
            }
            TermKind::PiType { binder, output } => self.resolve_pi_type(binder, output, span),
            TermKind::Lambda { binder, body } => self.resolve_lambda(binder, body, span),

            TermKind::Malformed => Err(TypeError::unsupported(span, "Malformed terms")),
            TermKind::Underscore => Err(TypeError::unsupported(span, "Type inference")),
        }
    }

    /// Resolves an identifier in the context. On success, returns the associated term as well as the number of
    /// binders between that binder's introduction and the current context - the binders in the term need to be
    /// increased by this number, which is done in [`resolve_identifier`][Self::resolve_identifier]
    fn resolve_path_inner(
        &self,
        path: Path,
        level_args: &LevelArgs,
        span: Span,
    ) -> Result<(TypedTerm, usize), TypeError> {
        match self {
            TypingContext::Root(env) => env.resolve_path(path, level_args, span).map(|t| (t, 0)),
            TypingContext::Binders { binders, parent } => {
                let (first, rest) = path.split_first();

                for (i, binder) in binders.iter().rev().enumerate() {
                    // Check whether the identifier matches the binder
                    if let Some(name) = binder.name {
                        if first == name {
                            // If the identifier resolved to the local variable but there are more segments in the path, give an error
                            if rest.is_some() {
                                return Err(TypeError {
                                    span,
                                    kind: TypeErrorKind::LocalVariableIsNotANamespace(
                                        OwnedPath::from_id(first),
                                    ),
                                });
                            }

                            // Local variables can't have level arguments
                            if level_args.count() != 0 {
                                return Err(TypeError {
                                    span,
                                    kind: TypeErrorKind::LevelArgumentGivenForLocalVariable(name),
                                });
                            }

                            return Ok((
                                TypedTerm::bound_variable(0, Some(first), binder.ty.clone(), span),
                                i,
                            ));
                        }
                    }
                }

                // If none of the binders matched, look up the path in the parent context
                parent
                    .resolve_path_inner(path, level_args, span)
                    .map(|(t, i)| (t, i + binders.len()))
            }
        }
    }

    /// Resolves a path in the current context
    fn resolve_path(
        &self,
        path: Path,
        level_args: &LevelArgs,
        span: Span,
    ) -> Result<TypedTerm, TypeError> {
        self.resolve_path_inner(path, level_args, span.clone())
            .map(|(t, i)| {
                // The term includes its own binder while the type doesn't, so the type needs to be incremented by one more than the term
                TypedTerm::value_of_type(
                    t.term().increment_above(0, i),
                    t.get_type().increment_above(0, i + 1),
                    span,
                )
                .with_abbreviation_from(&t)
            })
    }

    fn resolve_application(
        &self,
        function: &Term,
        argument: &Term,
        span: Span,
    ) -> Result<TypedTerm, TypeError> {
        let environment = self.environment();

        // Type check the function and argument
        let function = self.resolve_term(function)?;
        let argument = self.resolve_term(argument)?;

        // Reduce the type of the function
        let function_ty = environment.reduce_to_whnf(function.get_type());

        // Check that the function has a function type
        let Some((binder, output)) = function_ty.is_pi_type() else {
            return Err(TypeError {
                span: function.span(),
                kind: TypeErrorKind::NotAFunction(function),
            });
        };

        // Check that the type of the argument matches the input type of the function
        if !environment.def_eq(binder.ty.clone(), argument.get_type()) {
            return Err(environment.mismatched_types_error(argument, binder.ty.clone()));
        }

        // Replace instances of the binder in the output type with the argument
        let output_ty = output.replace_binder(0, &argument);

        Ok(TypedTerm::make_application(
            function, argument, output_ty, span,
        ))
    }

    fn resolve_pi_type(
        &self,
        binder: &Binder,
        output: &Term,
        span: Span,
    ) -> Result<TypedTerm, TypeError> {
        let [binder_name] = binder.names.as_slice() else {
            return Err(TypeError::unsupported(
                binder.span.clone(),
                "Multiple names in a binder",
            ));
        };

        // Resolve the type of the binder, and check that it actually is a type
        let binder_ty = self.resolve_term(&binder.ty)?;
        binder_ty.check_is_ty()?;
        let binder = TypedBinder {
            span: binder.span.clone(),
            name: *binder_name,
            ty: binder_ty,
        };

        // Construct a new typing context which includes the new binder
        let c = self.with_binder(&binder);

        // Resolve the output type in this new context
        let output = c.resolve_term(&output)?;
        output.check_is_ty()?;

        Ok(TypedTerm::make_pi_type(binder, output, span))
    }

    fn resolve_lambda(
        &self,
        binder: &Binder,
        body: &Term,
        span: Span,
    ) -> Result<TypedTerm, TypeError> {
        let [binder_name] = binder.names.as_slice() else {
            return Err(TypeError::unsupported(
                binder.span.clone(),
                "Multiple names in a binder",
            ));
        };

        // Resolve the type of the binder, and check that it actually is a type
        let binder_ty = self.resolve_term(&binder.ty)?;
        binder_ty.check_is_ty()?;

        let binder = TypedBinder {
            span: binder.span.clone(),
            name: *binder_name,
            ty: binder_ty,
        };

        // Construct a new typing context which includes the new binder
        let c = self.with_binder(&binder);

        // Resolve the output type in this new context
        let body = c.resolve_term(&body)?;

        Ok(TypedTerm::make_lambda(binder, body, span))
    }
}
