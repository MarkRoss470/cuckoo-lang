use super::{Abbreviation, TypedBinder, TypedTermKindInner};
use super::{TypedTerm, TypedTermKind};
use crate::typeck::TypingEnvironment;
use crate::typeck::data::Adt;
use crate::typeck::level::Level;
use parser::error::Span;
use std::iter;
use std::rc::Rc;

impl TypingEnvironment {
    /// Checks whether two terms are definitionally equal.
    pub fn def_eq(&self, l: TypedTerm, r: TypedTerm) -> bool {
        // If the terms are identical, then they are definitionally equal by reflexivity
        if l == r {
            return true;
        }
        // If both terms are sort literals, just check whether the levels are definitionally equal
        if let Some(ll) = l.is_sort_literal()
            && let Some(lr) = r.is_sort_literal()
        {
            return ll.def_eq(&lr);
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
                l.increment_above(0, 1),
                TypedTerm::bound_variable(0, None, binder.ty.clone(), binder.span()),
                output.clone(),
                l.span,
            ));

            let r = self.reduce_to_whnf(TypedTerm::make_application(
                r.increment_above(0, 1),
                TypedTerm::bound_variable(0, None, binder.ty.clone(), binder.span()),
                output.clone(),
                r.span,
            ));

            return self.def_eq(l, r);
        }

        // If none of the special cases apply, reduce the terms to WHNF and compare them structurally
        let l = self.reduce_to_whnf(l);
        let r = self.reduce_to_whnf(r);

        self.structural_def_eq(&l.term(), &r.term())
    }

    /// Converts a term to weak head normal form. This converts it to a form where its root can no
    /// longer be simplified by reducing applications of lambdas or recursors, although application
    /// arguments may still be reducible. If two terms are both in WHNF, then they can be checked
    /// for definitional equality by checking that they have the same form and checking definitional
    /// equality on the sub terms.
    #[must_use]
    pub fn reduce_to_whnf(&self, mut term: TypedTerm) -> TypedTerm {
        use TypedTermKindInner::*;

        let span = term.span();
        let mut args = vec![];

        // Repeatedly split the term into a function and its arguments,
        // then try to simplify by applying the function to one or more of the arguments.
        loop {
            let (function, mut new_args) = term.decompose_application_stack_reversed();
            args.append(&mut new_args);
            term = function.clone();

            match term.term().inner() {
                SortLiteral(_)
                | AdtName(_, _)
                | AdtConstructor(_, _, _)
                | BoundVariable { .. }
                | PiType { .. }
                | Axiom(_, _) => break,
                Lambda { .. } if args.is_empty() => break,
                Application { .. } => unreachable!(),

                // If the function is a lambda, apply one argument to it and reduce
                Lambda { binder, body } => {
                    let arg = args.pop().unwrap();
                    debug_assert!(self.def_eq(binder.ty.clone(), arg.get_type()));

                    term = self.reduce_to_whnf(body.replace_binder(0, &arg));

                    if let Some(abbr) = &body.term.abbreviation {
                        term = term
                            .with_abbreviation(Abbreviation::Application(abbr.clone(), arg.clone()))
                    }
                }
                // If the function is an ADT recursor, try to reduce it
                AdtRecursor(adt_index, _) => {
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
                        term.span(),
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
        TypedTerm::make_application_stack(term, args.into_iter().rev().map(|t| t.term()), span)
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
        span: Span,
    ) -> Option<TypedTerm> {
        debug_assert_eq!(args_reversed.len(), adt.recursor_num_parameters());

        // Accounts for the fact that `args_reversed` is in reverse order
        let get_recursor_arg = |i: usize| &args_reversed[args_reversed.len() - i - 1];

        // The recursor can only be reduced if the value parameter is an application of a constructor
        // TODO: subsingleton elimination
        let (value_fun, constructor_args) = self
            .reduce_to_whnf(get_recursor_arg(adt.recursor_value_param_index()).clone())
            .decompose_application_stack();
        let Some((adt_index, constructor_index, _)) = value_fun.is_adt_constructor() else {
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
            span,
        );

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
                span: binder.span(),
                name: binder.name,
                ty: reindex(i, binder.ty.clone()),
            })
            .collect();

        let value_param = TypedTerm::make_application_stack(
            param_val.clone(),
            param_params
                .into_iter()
                .cloned()
                .enumerate()
                .map(|(i, binder)| {
                    TypedTermKind::bound_variable(param_params.len() - i - 1, binder.name)
                }),
            param_val.span(),
        );

        let body = TypedTerm::make_application_stack(
            recursor.clone(),
            recursor_args_reversed
                .iter()
                .skip(adt.header.indices.len() + 1)
                .rev()
                .map(|t| t.term())
                .chain(iter::once(value_param.term())),
            recursor.span(),
        );

        TypedTerm::make_lambda_telescope(binders, body.clone(), body.span())
    }

    /// Compares whether two terms have the same top level structure, and checks the sub-terms for
    /// definitional equality if this is the case.
    fn structural_def_eq(&self, l: &TypedTermKind, r: &TypedTermKind) -> bool {
        use TypedTermKindInner::*;

        if l == r {
            return true;
        }

        match (l.inner(), r.inner()) {
            (SortLiteral(u1), SortLiteral(u2)) => u1.def_eq(&u2),
            (SortLiteral(_), _) => false,
            (AdtName(i1, l1), AdtName(i2, l2)) => i1 == i2 && l1 == l2,
            (AdtName(_, _), _) => false,
            (AdtConstructor(adt1, id1, l1), AdtConstructor(adt2, id2, l2)) => {
                adt1 == adt2 && id1 == id2 && l1 == l2
            }
            (AdtConstructor(_, _, _), _) => false,
            (AdtRecursor(adt1, l1), AdtRecursor(adt2, l2)) => adt1 == adt2 && l1 == l2,
            (AdtRecursor(_, _), _) => false,
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
            (Axiom(a1, l1), Axiom(a2, l2)) => a1 == a2 && l1 == l2,
            (Axiom(_, _), _) => false,
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

    pub fn fully_reduce(&self, term: TypedTerm, reduce_proofs: bool) -> TypedTerm {
        // If the term is a proof and should not be expanded, return it as-is
        if !reduce_proofs && term.level.def_eq(&Level::zero()) {
            return term;
        }

        let whnf_ty = self.reduce_to_whnf(term.get_type());
        let whnf_term = self.reduce_to_whnf(term.clone());
        let reduced_ty = self.fully_reduce_kind(&whnf_ty.term(), reduce_proofs);
        let reduced_term = self.fully_reduce_kind(&whnf_term.term(), reduce_proofs);

        let fully_reduced = TypedTerm::value_of_type(
            reduced_term,
            TypedTerm::value_of_type(
                reduced_ty,
                TypedTerm::sort_literal(term.level(), term.span()),
                term.span(),
            ),
            term.span(),
        );

        fully_reduced
    }

    fn fully_reduce_kind(
        &self,
        term: &Rc<TypedTermKind>,
        reduce_proofs: bool,
    ) -> Rc<TypedTermKind> {
        use TypedTermKindInner::*;

        match term.inner() {
            SortLiteral(_)
            | AdtName(_, _)
            | AdtConstructor(_, _, _)
            | AdtRecursor(_, _)
            | BoundVariable { .. }
            | Axiom(_, _) => term.clone(),

            Application { function, argument } => {
                let function = self.fully_reduce(function.clone(), reduce_proofs);
                let argument = self.fully_reduce(argument.clone(), reduce_proofs);
                TypedTermKind::application(function, argument)
            }
            PiType { binder, output } => {
                let binder = TypedBinder {
                    ty: self.fully_reduce(binder.ty.clone(), reduce_proofs),
                    ..binder.clone()
                };
                let output = self.fully_reduce(output.clone(), reduce_proofs);
                TypedTermKind::pi_type(binder, output)
            }
            Lambda { binder, body } => {
                let binder = TypedBinder {
                    ty: self.fully_reduce(binder.ty.clone(), reduce_proofs),
                    ..binder.clone()
                };
                let body = self.fully_reduce(body.clone(), reduce_proofs);
                TypedTermKind::lambda(binder, body)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use common::Interner;
    use parser::ast::parse_file;

    fn assert_def_eq(env: &mut TypingEnvironment, t1: &str, t2: &str) {
        let t1 = env.resolve_term_from_string(t1);
        let t2 = env.resolve_term_from_string(t2);

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

        let mut env = TypingEnvironment::new();
        env.load_str(context)
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

        let mut env = TypingEnvironment::new();
        env.load_str(context)
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
