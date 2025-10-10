use super::{TypedBinder, TypedTermKindInner};
use super::{TypedTerm, TypedTermKind};
use crate::typeck::TypingEnvironment;
use crate::typeck::data::{Adt, AdtConstructor};
use crate::typeck::level::Level;
use std::iter;

impl TypingEnvironment {
    /// Checks whether two terms are definitionally equal.
    pub fn def_eq(&self, l: TypedTerm, r: TypedTerm) -> bool {
        // If the terms are identical, then they are definitionally equal by reflexivity
        if l == r {
            return true;
        }
        // If both terms are sort literals, just check whether the levels are definitionally equal
        if let Some(l) = l.is_sort_literal()
            && let Some(r) = r.is_sort_literal()
        {
            return l.def_eq(&r);
        }
        // If the terms have different levels or different types, then they are not definitionally equal.
        if !l.level.def_eq(&r.level) || !self.def_eq(l.get_type(), r.get_type()) {
            return false;
        }

        // Any two values of the same type in `Prop` are definitionally equal
        if l.level == Level::zero() {
            return true;
        }

        let ty = self.reduce_to_whnf(l.get_type());

        // If the terms being compared are functions and at least one is a lambda,
        // compare them by applying them both to a fresh local variable and comparing the results.
        if let Some((binder, output)) = ty.is_pi_type()
            && (l.is_lambda().is_some() || r.is_lambda().is_some())
        {
            let l = self.reduce_to_whnf(TypedTerm::make_application(
                l.clone_incrementing(0, 1),
                TypedTerm::bound_variable(0, None, binder.ty.clone()),
                output.clone(),
            ));

            let r = self.reduce_to_whnf(TypedTerm::make_application(
                r.clone_incrementing(0, 1),
                TypedTerm::bound_variable(0, None, binder.ty.clone()),
                output.clone(),
            ));

            return self.def_eq(l, r);
        }

        // If none of the special cases apply, reduce the terms to WHNF and compare them structurally
        let l = self.reduce_to_whnf(l);
        let r = self.reduce_to_whnf(r);

        self.pretty_println_val(&l);
        self.pretty_println_val(&r);

        self.structural_def_eq(l.term(), r.term())
    }

    /// Converts a term to weak head normal form. This converts it to a form where its root can no
    /// longer be simplified by reducing applications of lambdas or recursors, although application
    /// arguments may still be reducible. If two terms are both in WHNF, then they can be checked
    /// for definitional equality by checking that they have the same form and checking definitional
    /// equality on the sub terms.
    #[must_use]
    pub fn reduce_to_whnf(&self, mut term: TypedTerm) -> TypedTerm {
        use TypedTermKindInner::*;

        let mut args = vec![];

        // Repeatedly split the term into a function and its arguments,
        // then try to simplify by applying the function to one or more of the arguments.
        loop {
            let (function, mut new_args) = term.decompose_application_stack_reversed();
            args.append(&mut new_args);
            term = function.clone();

            match term.term().inner() {
                SortLiteral(_)
                | AdtName(_)
                | AdtConstructor(_, _)
                | BoundVariable { .. }
                | PiType { .. } => break,
                Lambda { .. } if args.is_empty() => break,
                Application { .. } => unreachable!(),

                // If the function is a lambda, apply one argument to it and reduce
                Lambda { binder, body } => {
                    let arg = args.pop().unwrap();
                    debug_assert!(self.def_eq(binder.ty.clone(), arg.get_type()));

                    term = self.reduce_to_whnf(body.replace_binder(0, &arg));
                }
                // If the function is an ADT recursor, try to reduce it
                AdtRecursor(adt_index) => {
                    let adt = self.get_adt(*adt_index);
                    // Reducing a recursor requires all the arguments to be known
                    if args.len() < adt.recursor_num_parameters() {
                        break;
                    }

                    // Attempt to reduce the recursor application
                    let Some(t) = self.try_to_reduce_recursor_application(
                        adt,
                        &function,
                        &args[args.len() - adt.recursor_num_parameters()..],
                    ) else {
                        break;
                    };

                    // The reduction has used up the innermost arguments of the application,
                    // so remove them from `args`
                    args.drain(args.len() - adt.recursor_num_parameters()..);

                    term = t;
                }
            }
        }

        // Once the term can't be reduced further, re-apply the arguments
        TypedTerm::make_application_stack(term, args.into_iter().rev().map(|t| t.term()))
    }

    /// Attempts to reduce the application of a recursor applied to the given arguments.
    /// If the reduction is successful, the reduced term is returned, otherwise the return value is
    /// `None`.
    ///
    /// Reduction succeeds if the value parameter reduces to an application of a constructor.
    /// The output is of the form `<induction rule> <args> <inductive arguments>`,
    /// where `<induction rule>` is the argument to the recursor corresponding to the induction
    /// rule for the constructor in question.
    ///
    /// See [`Self::make_recursor_application_inductive_argument`] for the format of inductive arguments.
    #[must_use]
    fn try_to_reduce_recursor_application(
        &self,
        adt: &Adt,
        recursor: &TypedTerm,
        args_reversed: &[TypedTerm],
    ) -> Option<TypedTerm> {
        debug_assert_eq!(args_reversed.len(), adt.recursor_num_parameters());

        // Accounts for the fact that `args_reversed` is in reverse order
        let get_recursor_arg = |i: usize| &args_reversed[args_reversed.len() - i - 1];

        // The recursor can only be reduced if the value parameter is an application of a constructor
        // TODO: subsingleton elimination
        let (value_fun, constructor_args) = self
            .reduce_to_whnf(get_recursor_arg(adt.recursor_value_param_index()).clone())
            .decompose_application_stack();
        let Some((adt_index, constructor_index)) = value_fun.is_adt_constructor() else {
            return None;
        };

        let constructor = &adt.constructors[constructor_index];

        debug_assert_eq!(adt.header.index, adt_index);
        debug_assert_eq!(
            constructor_args.len(),
            adt.header.parameters.len() + constructor.params.len()
        );

        // Get the induction rule for the constructor being reduced
        let induction_rule =
            get_recursor_arg(adt.recursor_constructor_param_index(constructor_index)).clone();

        let output = TypedTerm::make_application_stack(
            induction_rule,
            constructor_args
                .iter()
                .skip(adt.header.parameters.len())
                .map(|arg| arg.term().clone())
                .chain(constructor.inductive_params().map(
                    |(param_index, param_params, param_indices)| {
                        self.make_recursor_application_inductive_argument(
                            adt,
                            recursor,
                            args_reversed,
                            &constructor_args,
                            param_index,
                            constructor_args[adt.header.parameters.len() + param_index].clone(),
                            param_params,
                            param_indices,
                        )
                        .term()
                    },
                )),
        );

        self.pretty_println_val(&output);

        Some(output)
    }

    /// Constructs an inductive argument for a given inductive constructor parameter
    /// when reducing a recursor.
    ///
    /// The format of the returned value is:
    /// `fun <param_params> => <recursor> <motive> <constructor rules> <indices> (<parameter> <param_params>)`
    /// Where the motive and constructor rules are the same as in the recursor application being
    /// reduced,
    #[must_use]
    fn make_recursor_application_inductive_argument(
        &self,
        adt: &Adt,
        recursor: &TypedTerm,
        recursor_args_reversed: &[TypedTerm],
        constructor_args: &[TypedTerm],
        param_index: usize,
        param_val: TypedTerm,
        param_params: &[TypedBinder],
        param_indices: &[TypedTerm],
    ) -> TypedTerm {
        debug_assert_eq!(
            param_indices.len(),
            adt.header.parameters.len() + adt.header.indices.len()
        );

        let reindex = |i, mut term: TypedTerm| {
            for constructor_arg in &constructor_args[..param_index] {
                term = term.replace_binder(i, constructor_arg)
            }
            for adt_param in recursor_args_reversed
                [recursor_args_reversed.len() - adt.header.parameters.len() - 1..]
                .iter()
                .rev()
            {
                term = term.replace_binder(i, adt_param);
            }

            term
        };

        let binders: Vec<_> = param_params
            .iter()
            .enumerate()
            .map(|(i, binder)| TypedBinder {
                name: binder.name,
                ty: reindex(i, binder.ty.clone()),
            })
            .collect();

        let value_param = TypedTerm::make_application_stack(
            param_val,
            param_params
                .into_iter()
                .cloned()
                .enumerate()
                .map(|(i, binder)| {
                    TypedTermKind::bound_variable(param_params.len() - i - 1, binder.name)
                }),
        );

        let body = TypedTerm::make_application_stack(
            recursor.clone(),
            recursor_args_reversed
                .iter()
                .skip(adt.header.indices.len() + 1)
                .rev()
                .map(|t| t.term())
                .chain(iter::once(value_param.term())),
        );

        TypedTerm::make_lambda_telescope(binders, body)
    }

    /// Compares whether two terms have the same top level structure, and checks the sub-terms for
    /// definitional equality if this is the case.
    fn structural_def_eq(&self, l: TypedTermKind, r: TypedTermKind) -> bool {
        use TypedTermKindInner::*;

        if l == r {
            return true;
        }

        match (l.inner(), r.inner()) {
            (SortLiteral(su), SortLiteral(ou)) => su.def_eq(&ou),
            (SortLiteral(_), _) => false,
            (AdtName(sid), AdtName(oid)) => sid == oid,
            (AdtName(_), _) => false,
            (AdtConstructor(sadt, sid), AdtConstructor(oadt, oid)) => sadt == oadt && sid == oid,
            (AdtConstructor(_, _), _) => false,
            (AdtRecursor(sadt), AdtRecursor(oadt)) => sadt == oadt,
            (AdtRecursor(_), _) => false,
            (
                BoundVariable {
                    index: sid,
                    name: _,
                },
                BoundVariable {
                    index: oid,
                    name: _,
                },
            ) => sid == oid,
            (BoundVariable { .. }, _) => false,
            (
                Application {
                    function: sf,
                    argument: sa,
                },
                Application {
                    function: of,
                    argument: oa,
                },
            ) => self.def_eq(sf.clone(), of.clone()) && self.def_eq(sa.clone(), oa.clone()),
            (Application { .. }, _) => false,
            (
                PiType {
                    binder: sb,
                    output: so,
                },
                PiType {
                    binder: ob,
                    output: oo,
                },
            ) => self.def_eq(sb.ty.clone(), ob.ty.clone()) && self.def_eq(so.clone(), oo.clone()),
            (PiType { .. }, _) => false,
            (
                Lambda {
                    binder: _,
                    body: sbo,
                },
                Lambda {
                    binder: _,
                    body: obo,
                },
            ) => self.def_eq(sbo.clone(), obo.clone()),
            (Lambda { .. }, _) => false,
        }
    }

    pub fn fully_reduce(&self, term: TypedTerm) -> TypedTerm {
        let ty = self.fully_reduce_kind(&self.reduce_to_whnf(term.get_type()).term());
        let t = self.fully_reduce_kind(&self.reduce_to_whnf(term.clone()).term());

        TypedTerm::value_of_type(
            TypedTermKind::from_inner(t),
            TypedTerm::value_of_type(
                TypedTermKind::from_inner(ty),
                TypedTerm::sort_literal(term.level),
            ),
        )
    }

    fn fully_reduce_kind(&self, term: &TypedTermKind) -> TypedTermKindInner {
        use TypedTermKindInner::*;

        let inner = match term.inner() {
            inner @ (SortLiteral(_)
            | AdtName(_)
            | AdtConstructor(_, _)
            | AdtRecursor(_)
            | BoundVariable { .. }) => inner.clone(),

            Application { function, argument } => {
                let function = self.fully_reduce(function.clone());
                let argument = self.fully_reduce(argument.clone());
                Application { function, argument }
            }
            PiType { binder, output } => {
                let binder = TypedBinder {
                    ty: self.fully_reduce(binder.ty.clone()),
                    ..binder.clone()
                };
                let output = self.fully_reduce(output.clone());
                PiType { binder, output }
            }
            Lambda { binder, body } => {
                let binder = TypedBinder {
                    ty: self.fully_reduce(binder.ty.clone()),
                    ..binder.clone()
                };
                let body = self.fully_reduce(body.clone());
                Lambda { binder, body }
            }
        };
        inner
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::ast::parse_file;

    fn assert_def_eq(env: &mut TypingEnvironment, t1: &str, t2: &str) {
        let t1 = env.resolve_term_from_string(t1);
        let t2 = env.resolve_term_from_string(t2);

        env.pretty_println_val(&t1);
        env.pretty_println_val(&env.reduce_to_whnf(t1.clone()));
        env.pretty_println_val(&t2);

        assert!(env.def_eq(t1, t2));
    }

    fn assert_not_def_eq(env: &mut TypingEnvironment, t1: &str, t2: &str) {
        let t1 = env.resolve_term_from_string(t1);
        let t2 = env.resolve_term_from_string(t2);

        assert!(!env.def_eq(t1, t2));
    }

    #[test]
    fn test_def_eq() {
        let context = r"
            data Nat : Type where
              | zero : Nat
              | succ : Nat -> Nat

            data P : Prop where
              | c1 : P
              | c2 : P
        ";

        let (interner, file) = parse_file(context).unwrap();
        let mut env = TypingEnvironment::new(interner);
        env.resolve_file(&file)
            .expect("Environment should have type checked");

        // Concrete terms
        assert_def_eq(&mut env, "Nat.zero", "Nat.zero");
        assert_def_eq(&mut env, "(Nat.succ) Nat.zero", "Nat.succ (Nat.zero)");
        assert_def_eq(&mut env, "Nat.succ", "Nat.succ");

        assert_not_def_eq(&mut env, "Nat.zero", "Nat.succ Nat.zero");
        assert_not_def_eq(&mut env, "Nat.succ", "fun (x : Nat) => Nat.zero");

        // Function application
        assert_def_eq(&mut env, "Nat.zero", "(fun (x : Nat) => Nat.zero) Nat.zero");
        assert_def_eq(
            &mut env,
            "(fun (f : Nat -> Nat) => fun (x : Nat) => f (f x)) (fun (x : Nat) => Nat.succ x)",
            "fun (x : Nat) => Nat.succ (Nat.succ x)",
        );
        assert_def_eq(
            &mut env,
            "(fun (f : Nat -> Nat) => f (f Nat.zero)) (fun (x : Nat) => Nat.succ x)",
            "Nat.succ (Nat.succ Nat.zero)",
        );

        // A lambda which immediately applies its argument is equal to the function it applies it to
        assert_def_eq(&mut env, "Nat.succ", "fun (x : Nat) => Nat.succ x");
        assert_def_eq(
            &mut env,
            "fun (f : Nat -> Nat) => f",
            "fun (f : Nat -> Nat) => fun (x : Nat) => f x",
        );
        assert_def_eq(
            &mut env,
            "fun (f : Nat -> Nat -> Nat) => fun (x : Nat) => fun (y : Nat) => f x y",
            "fun (f : Nat -> Nat -> Nat) => f",
        );

        // It is order that matters, not the name of the variable
        assert_not_def_eq(
            &mut env,
            "fun (x : Nat) => fun (y : Nat) => x",
            "fun (x : Nat) => fun (y : Nat) => y",
        );
        assert_def_eq(
            &mut env,
            "fun (x : Nat) => fun (y : Nat) => x",
            "fun (y : Nat) => fun (x : Nat) => y",
        );

        // Terms in a Prop type are all definitionally equal
        assert_def_eq(&mut env, "P.c1", "P.c1");
        assert_def_eq(&mut env, "P.c2", "P.c2");
        assert_def_eq(&mut env, "P.c1", "P.c2");
        assert_def_eq(
            &mut env,
            "fun (x : P) => fun (y : P) => x",
            "fun (x : P) => fun (y : P) => y",
        );
        assert_def_eq(
            &mut env,
            "fun (x : P) => fun (y : P) => x",
            "fun (x : P) => fun (y : P) => P.c1",
        );
    }

    #[test]
    fn test_recursor_reduction() {
        let context = r"
            data Nat : Type where
              | zero : Nat
              | succ : Nat -> Nat
    
            data List (T : Type) : Type where
              | nil : List T
              | cons : T -> List T -> List T
            
            def Nat.one : Nat := Nat.succ Nat.zero
            def Nat.two : Nat := Nat.succ Nat.one
            def Nat.three : Nat := Nat.succ Nat.two

            def list_012 : List Nat := List.cons Nat Nat.zero (List.cons Nat Nat.one (List.cons Nat Nat.two   (List.nil Nat)))
            def list_123 : List Nat := List.cons Nat Nat.one  (List.cons Nat Nat.two (List.cons Nat Nat.three (List.nil Nat)))
        ";

        let (interner, file) = parse_file(context).unwrap();
        let mut env = TypingEnvironment::new(interner);
        env.resolve_file(&file)
            .expect("Environment should have type checked");

        assert_def_eq(
            &mut env,
            "Nat.rec.{1}
                (fun (x : Nat) => Nat) 
                Nat.zero 
                (fun (_n : Nat) => fun (d : Nat) => Nat.succ (Nat.succ d)) 
                (Nat.succ (Nat.succ Nat.zero))",
            "Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))",
        );

        assert_def_eq(
            &mut env,
            "List.rec.{1} Nat
                (fun (x : List Nat) => List Nat)
                (List.nil Nat)
                (fun (x : Nat) => fun (xs : List Nat) => fun (m : List Nat) => List.cons Nat (Nat.succ x) m)
                list_012",
            "list_123",
        );
    }
}
