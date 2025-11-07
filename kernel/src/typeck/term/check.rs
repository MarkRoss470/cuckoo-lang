//! The [`check_term`] method to double-check the correctness of a term
//!
//! [`check_term`]: TypingEnvironment::check_term

use crate::typeck::level::{Level, LevelArgs};
use crate::typeck::term::{TypedBinder, TypedTerm, TypedTermKindInner};
use crate::typeck::{AdtIndex, AxiomIndex, PrettyPrintContext, TypingEnvironment};
use common::{Identifier, PrettyPrint};
use parser::atoms::ident::Path;
use std::io::Write;

/// A context to map bound variables to the type of the binder they reference
enum CheckContext<'a> {
    /// There are no bound variables yet
    Root,
    /// Records the type of one binder, and stores a reference to a parent context for the rest.
    Binder {
        /// The type of the binder
        ty: &'a TypedTerm,
        /// The parent context. Variables with an index greater than 0 will be looked up in the
        /// parent, with the id reduced by 1
        parent: &'a CheckContext<'a>,
    },
}

impl<'a> CheckContext<'a> {
    /// Gets the type of the bound variable with index `id`. If `id` is greater than the number
    /// of bound variables in scope, returns `None`.
    ///
    /// Binders in the returned type are correct for its definition.
    fn get_type_of_binder_inner(&self, id: usize) -> Option<&TypedTerm> {
        match self {
            CheckContext::Root => None,
            CheckContext::Binder { ty, parent } => {
                if id == 0 {
                    Some(ty)
                } else {
                    parent.get_type_of_binder_inner(id - 1)
                }
            }
        }
    }

    /// Gets the type of the bound variable with index `id`. If `id` is greater than the number
    /// of bound variables in scope, returns `None`.
    ///
    /// Binders in the returned type are correct for its use.
    fn get_type_of_binder(&self, id: usize) -> Option<TypedTerm> {
        self.get_type_of_binder_inner(id)
            .map(|t| t.increment_above(0, id + 1))
    }
}

impl TypingEnvironment {
    /// Double-checks a term for correctness. If this check fails, this indicates a bug in the kernel,
    /// so the method panics rather than returning an error.
    pub fn check_term(&self, term: &TypedTerm) {
        self.check_term_with_context(term, &CheckContext::Root);
    }

    /// Check a term for correctness in a given context
    fn check_term_with_context(&self, term: &TypedTerm, context: &CheckContext) {
        use TypedTermKindInner::*;

        // If the term has been checked before, don't check it again
        if term.term.cached_properties.checked.get() {
            #[cfg(feature = "track-stats")]
            self.stats.check_cache_hits.update(|n| n + 1);
            return;
        }

        #[cfg(feature = "track-stats")]
        self.stats.check_cache_misses.update(|n| n + 1);

        // If the term is not itself a type, check its type for correctness
        if term.get_type().is_sort_literal().is_none() {
            self.check_term_with_context(&term.get_type(), context);
        }

        // Compute what the type of the term should be, while checking its sub-terms for correctness.
        let true_ty = match term.term().inner() {
            SortLiteral(l) => Self::deduce_sort_literal_type(term, l),
            AdtName(adt, level_args) => self.deduce_adt_name_type(term, adt, level_args),
            AdtConstructor(adt, constructor, level_args) => {
                self.deduce_adt_constructor_type(term, adt, constructor, level_args)
            }
            AdtRecursor(adt, level_args) => self.deduce_adt_recursor_type(term, adt, level_args),
            Axiom(axiom, level_args) => self.deduce_axiom_type(term, axiom, level_args),
            BoundVariable { index, name: _ } => {
                self.deduce_bound_variable_type(term, context, index)
            }
            Application { function, argument } => {
                self.deduce_application_type(term, context, function, argument)
            }
            PiType { binder, output } => self.deduce_pi_type_type(term, context, binder, output),
            Lambda { binder, body } => self.deduce_lambda_type(term, context, binder, body),
        };

        // Check that the computed type is definitionally equal to `term.ty`
        if !term.level.def_eq(&true_ty.check_is_ty().unwrap())
            || !self.def_eq(term.get_type(), true_ty.clone())
        {
            println!("Term:");
            self.pretty_println_val_with_proofs(term);
            println!("Actual type:");
            self.pretty_println_val(&term.get_type());
            println!("Expected type:");
            self.pretty_println_val(&true_ty);
            println!("Binders:");
            self.pretty_println_val(context);

            panic!("Invalid term found")
        }

        // Cache that the term has been checked
        term.term.cached_properties.checked.set(true);
    }

    /// Checks a [`SortLiteral`] term while computing its correct type
    ///
    /// [`SortLiteral`]: TypedTermKindInner::SortLiteral
    fn deduce_sort_literal_type(term: &TypedTerm, l: &Level) -> TypedTerm {
        assert_eq!(term.term.cached_properties.indices_less_than, 0);
        assert_eq!(
            term.term.cached_properties.mentions_level_parameter,
            l.mentions_parameters()
        );
        TypedTerm::sort_literal(l.succ(), term.span())
    }

    /// Checks an [`AdtName`] term while computing its correct type
    ///
    /// [`AdtName`]: TypedTermKindInner::AdtName
    fn deduce_adt_name_type(
        &self,
        term: &TypedTerm,
        adt: &AdtIndex,
        level_args: &LevelArgs,
    ) -> TypedTerm {
        assert_eq!(term.term.cached_properties.indices_less_than, 0);
        assert_eq!(
            term.term.cached_properties.mentions_level_parameter,
            level_args.mentions_parameters()
        );

        let adt_name = self.get_adt(*adt).header.name.borrow();
        self.root
            .resolve(adt_name, level_args, term.span())
            .unwrap()
            .get_type()
    }

    /// Checks an [`AdtConstructor`] term while computing its correct type
    ///
    /// [`AdtConstructor`]: TypedTermKindInner::AdtConstructor
    fn deduce_adt_constructor_type(
        &self,
        term: &TypedTerm,
        adt: &AdtIndex,
        constructor: &usize,
        level_args: &LevelArgs,
    ) -> TypedTerm {
        assert_eq!(term.term.cached_properties.indices_less_than, 0);
        assert_eq!(
            term.term.cached_properties.mentions_level_parameter,
            level_args.mentions_parameters()
        );

        let adt = self.get_adt(*adt);
        let adt_name = adt.header.name.borrow();
        let constructor_name = adt.constructors[*constructor].name;
        let adt_ns = self.root.resolve_namespace(adt_name, term.span()).unwrap();
        adt_ns
            .resolve(Path::from_id(&constructor_name), level_args, term.span())
            .unwrap()
            .get_type()
    }

    /// Checks an [`AdtRecursor`] term while computing its correct type
    ///
    /// [`AdtRecursor`]: TypedTermKindInner::AdtRecursor
    fn deduce_adt_recursor_type(
        &self,
        term: &TypedTerm,
        adt: &AdtIndex,
        level_args: &LevelArgs,
    ) -> TypedTerm {
        assert_eq!(term.term.cached_properties.indices_less_than, 0);
        assert_eq!(
            term.term.cached_properties.mentions_level_parameter,
            level_args.mentions_parameters()
        );

        let adt = self.get_adt(*adt);
        let adt_name = adt.header.name.borrow();
        let adt_ns = self.root.resolve_namespace(adt_name, term.span()).unwrap();
        adt_ns
            .resolve(
                Path::from_id(&Identifier::from_str(
                    "rec",
                    &mut self.interner.borrow_mut(),
                )),
                level_args,
                term.span(),
            )
            .unwrap()
            .get_type()
    }

    /// Checks an [`Axiom`] term while computing its correct type
    ///
    /// [`Axiom`]: TypedTermKindInner::Axiom
    fn deduce_axiom_type(
        &self,
        term: &TypedTerm,
        axiom: &AxiomIndex,
        level_args: &LevelArgs,
    ) -> TypedTerm {
        assert_eq!(term.term.cached_properties.indices_less_than, 0);
        assert_eq!(
            term.term.cached_properties.mentions_level_parameter,
            level_args.mentions_parameters()
        );

        self.get_axiom(*axiom).ty.instantiate(level_args)
    }

    /// Checks a [`BoundVariable`] term while computing its correct type
    ///
    /// [`BoundVariable`]: TypedTermKindInner::BoundVariable
    fn deduce_bound_variable_type(
        &self,
        term: &TypedTerm,
        context: &CheckContext,
        index: &usize,
    ) -> TypedTerm {
        assert_eq!(term.term.cached_properties.indices_less_than, index + 1);
        assert!(!term.term.cached_properties.mentions_level_parameter);

        match context.get_type_of_binder(*index).clone() {
            // If the index is too large, panic
            None => {
                println!("Binders:");
                self.pretty_println_val(context);
                panic!("Term referenced bound variable with index {index}, which is too large.")
            }
            Some(t) => t,
        }
    }

    /// Checks an [`Application`] term while computing its correct type
    ///
    /// [`Application`]: TypedTermKindInner::Application
    fn deduce_application_type(
        &self,
        term: &TypedTerm,
        context: &CheckContext,
        function: &TypedTerm,
        argument: &TypedTerm,
    ) -> TypedTerm {
        assert_eq!(
            term.term.cached_properties.indices_less_than,
            union_cached_indices_less_than(function, argument)
        );
        assert_eq!(
            term.term.cached_properties.mentions_level_parameter,
            union_cached_mentions_level_parameter(function, argument)
        );

        self.check_term_with_context(function, context);
        self.check_term_with_context(argument, context);

        let function_ty = self.reduce_to_whnf(function.get_type());
        let (binder, output) = function_ty.is_pi_type().unwrap();

        assert!(self.def_eq(binder.ty, argument.get_type()));

        output.replace_binder(0, argument)
    }

    /// Checks a [`PiType`] term while computing its correct type
    ///
    /// [`PiType`]: TypedTermKindInner::PiType
    fn deduce_pi_type_type(
        &self,
        term: &TypedTerm,
        context: &CheckContext,
        binder: &TypedBinder,
        output: &TypedTerm,
    ) -> TypedTerm {
        assert_eq!(
            term.term.cached_properties.indices_less_than,
            union_bound_cached_indices_less_than(binder, output)
        );
        assert_eq!(
            term.term.cached_properties.mentions_level_parameter,
            union_cached_mentions_level_parameter(&binder.ty, output)
        );

        self.check_term_with_context(&binder.ty, context);
        self.check_term_with_context(
            output,
            &CheckContext::Binder {
                ty: &binder.ty,
                parent: context,
            },
        );

        TypedTerm::sort_literal(
            Level::smart_imax(
                &binder.ty.check_is_ty().unwrap(),
                &output.check_is_ty().unwrap(),
            ),
            term.span(),
        )
    }

    /// Checks a [`Lambda`] term while computing its correct type
    ///
    /// [`Lambda`]: TypedTermKindInner::Lambda
    fn deduce_lambda_type(
        &self,
        term: &TypedTerm,
        context: &CheckContext,
        binder: &TypedBinder,
        body: &TypedTerm,
    ) -> TypedTerm {
        assert_eq!(
            term.term.cached_properties.indices_less_than,
            union_bound_cached_indices_less_than(binder, body)
        );
        assert_eq!(
            term.term.cached_properties.mentions_level_parameter,
            union_cached_mentions_level_parameter(&binder.ty, body)
        );

        self.check_term_with_context(&binder.ty, context);
        self.check_term_with_context(
            body,
            &CheckContext::Binder {
                ty: &binder.ty,
                parent: context,
            },
        );

        TypedTerm::make_pi_type(binder.clone(), body.get_type(), term.span())
    }
}

/// Finds the maximum of the cached [`indices_less_than`] property across two [`TypedTerm`]s
///
/// [`indices_less_than`]: crate::typeck::term::CachedTermProperties::indices_less_than
fn union_cached_indices_less_than(t1: &TypedTerm, t2: &TypedTerm) -> usize {
    t1.term
        .cached_properties
        .indices_less_than
        .max(t1.ty.cached_properties.indices_less_than)
        .max(t2.term.cached_properties.indices_less_than)
        .max(t2.ty.cached_properties.indices_less_than)
}

/// Finds the maximum of the cached [`indices_less_than`] property across a binder [`TypedTerm`]
/// and a term bound by that binder
///
/// [`indices_less_than`]: crate::typeck::term::CachedTermProperties::indices_less_than
fn union_bound_cached_indices_less_than(b: &TypedBinder, t: &TypedTerm) -> usize {
    b.ty.term
        .cached_properties
        .indices_less_than
        .max(b.ty.ty.cached_properties.indices_less_than)
        // Subtract one from the values from the bound term because the binder adds 1 to all indices
        .max(t.term.cached_properties.indices_less_than.saturating_sub(1))
        .max(t.ty.cached_properties.indices_less_than.saturating_sub(1))
}

/// Finds the logical or of the cached [`mentions_level_parameter`] property across two [`TypedTerm`]s
///
/// [`mentions_level_parameter`]: crate::typeck::term::CachedTermProperties::mentions_level_parameter
fn union_cached_mentions_level_parameter(t1: &TypedTerm, t2: &TypedTerm) -> bool {
    t1.term.cached_properties.mentions_level_parameter
        || t1.ty.cached_properties.mentions_level_parameter
        || t2.term.cached_properties.mentions_level_parameter
        || t2.ty.cached_properties.mentions_level_parameter
}

impl<'a> PrettyPrint<(usize, PrettyPrintContext<'a>)> for CheckContext<'a> {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        (id, context): (usize, PrettyPrintContext),
    ) -> std::io::Result<()> {
        match self {
            CheckContext::Root => Ok(()),
            CheckContext::Binder { ty, parent } => {
                write!(out, "{id}: ")?;
                ty.pretty_print(out, context)?;
                writeln!(out)?;
                parent.pretty_print(out, (id + 1, context))
            }
        }
    }
}

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for CheckContext<'a> {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext,
    ) -> std::io::Result<()> {
        self.pretty_print(out, (0, context))
    }
}
