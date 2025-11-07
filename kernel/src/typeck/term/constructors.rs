//! Constructor methods for [`TypedTerm`] and [`TypedTermKind`]

use crate::typeck::level::{Level, LevelArgs};
use crate::typeck::term::{
    Abbreviation, CachedTermProperties, TypedBinder, TypedTerm, TypedTermKind, TypedTermKindInner,
};
use crate::typeck::{AdtIndex, AxiomIndex};
use common::Identifier;
use parser::error::Span;
use std::cell::Cell;
use std::rc::Rc;

impl TypedTerm {
    /// Constructs a term with a given value and type
    pub fn value_of_type(value: Rc<TypedTermKind>, ty: TypedTerm, span: Span) -> TypedTerm {
        TypedTerm {
            span,
            level: ty.check_is_ty().expect("`ty` should have been a type"),
            ty: ty.term.clone(),
            term: value,
        }
    }

    /// Constructs a term representing the sort literal `Sort <level>`
    pub fn sort_literal(level: Level, span: Span) -> TypedTerm {
        TypedTerm {
            span,
            level: level.succ().succ(),
            ty: TypedTermKind::sort_literal(level.succ()),
            term: TypedTermKind::sort_literal(level),
        }
    }

    /// Constructs a term referring to the name of an ADT
    pub fn adt_name(
        adt_index: AdtIndex,
        ty: TypedTerm,
        level_args: LevelArgs,
        span: Span,
    ) -> TypedTerm {
        TypedTerm::value_of_type(TypedTermKind::adt_name(adt_index, level_args), ty, span)
    }

    /// Constructs a term referring to a constructor of an ADT
    pub fn adt_constructor(
        adt_index: AdtIndex,
        constructor: usize,
        ty: TypedTerm,
        level_args: LevelArgs,
        span: Span,
    ) -> TypedTerm {
        TypedTerm::value_of_type(
            TypedTermKind::adt_constructor(adt_index, constructor, level_args),
            ty,
            span,
        )
    }

    /// Constructs a term referring to the recursor of an ADT
    pub fn adt_recursor(
        adt_index: AdtIndex,
        ty: TypedTerm,
        level_args: LevelArgs,
        span: Span,
    ) -> TypedTerm {
        TypedTerm::value_of_type(TypedTermKind::adt_recursor(adt_index, level_args), ty, span)
    }

    /// Constructs a term referring to an axiom
    pub fn axiom(
        axiom_index: AxiomIndex,
        ty: TypedTerm,
        level_args: LevelArgs,
        span: Span,
    ) -> TypedTerm {
        TypedTerm::value_of_type(TypedTermKind::axiom(axiom_index, level_args), ty, span)
    }

    /// Constructs a term referring to a bound variable. The given `ty` is used as-is, so the indices
    /// in it should be incremented from the type in the variable's binder.
    pub fn bound_variable(
        index: usize,
        name: Option<Identifier>,
        ty: TypedTerm,
        span: Span,
    ) -> TypedTerm {
        TypedTerm::value_of_type(TypedTermKind::bound_variable(index, name), ty, span)
    }

    /// Constructs a term referring to an application of a function to an argument
    pub fn make_application(
        function: TypedTerm,
        argument: TypedTerm,
        output: TypedTerm,
        span: Span,
    ) -> TypedTerm {
        TypedTerm::value_of_type(TypedTermKind::application(function, argument), output, span)
    }

    /// Constructs a term referring to a pi type with the given binder and output
    ///
    /// # Panics
    /// If `binder.ty` or `output` are not types
    pub fn make_pi_type(binder: TypedBinder, output: TypedTerm, span: Span) -> TypedTerm {
        let binder_level = binder
            .ty
            .check_is_ty()
            .expect("`binder.ty` should have been a type");
        let output_level = output
            .ty
            .check_is_sort()
            .expect("`output` should have been a type");
        let level = binder_level.smart_imax(&output_level);

        TypedTerm {
            span,
            level: level.succ(),
            ty: TypedTermKind::sort_literal(level),
            term: TypedTermKind::pi_type(binder, output),
        }
    }

    /// Constructs a term referring to a lambda abstraction with the given binder and body
    ///
    /// # Panics
    /// If `binder.ty` is not a type.
    pub fn make_lambda(binder: TypedBinder, body: TypedTerm, span: Span) -> TypedTerm {
        TypedTerm::value_of_type(
            TypedTermKind::lambda(binder.clone(), body.clone()),
            TypedTerm::make_pi_type(binder, body.get_type(), span.clone()),
            span,
        )
    }

    /// Constructs a term representing a function applied to multiple arguments.
    ///
    /// # Parameters
    /// * `function`: The function term
    /// * `arguments`: An iterator over the arguments to the function in source order. The types
    ///   of these arguments are inferred from the type of `function`.
    /// * `span`: The source span which will be used for all application terms in the output
    ///
    /// # Panics
    /// If `function` is applied to more arguments than it has parameters. `function` is not reduced,
    /// so its type must be a telescope of pi types with at least as many nested pi types as there
    /// are arguments.
    pub fn make_application_stack(
        function: TypedTerm,
        arguments: impl IntoIterator<Item = Rc<TypedTermKind>>,
        span: Span,
    ) -> TypedTerm {
        let mut res = function;

        for argument in arguments {
            let TypedTermKindInner::PiType { binder, output } = res.ty.clone_inner() else {
                panic!("`res` should have been a function type")
            };

            let argument = TypedTerm::value_of_type(argument, binder.ty, span.clone());
            let output = output.replace_binder(0, &argument);
            res = TypedTerm::make_application(res, argument, output, span.clone());
        }

        res
    }

    /// Constructs a term representing a telescope of pi types.
    ///
    /// # Parameters
    /// * `binders`: an iterator over the telescope's binders in source order (although it must be
    ///   reversible as the binders will be used in the reverse of this order)
    /// * `output`: the output of the telescope.
    /// * `span`: The source span which will be used for all pi types in the output
    ///
    /// # Panics
    /// If the [`ty`] field of any element of `binders` is not a type, or if `output` is not a type.
    ///
    /// [`ty`]: TypedBinder::ty
    pub fn make_telescope(
        binders: impl IntoIterator<IntoIter: DoubleEndedIterator<Item = TypedBinder>>,
        output: TypedTerm,
        span: Span,
    ) -> TypedTerm {
        binders.into_iter().rfold(output, |acc, binder| {
            TypedTerm::make_pi_type(binder, acc, span.clone())
        })
    }

    /// Constructs a term representing a telescope of lambda abstractions.
    ///
    /// # Parameters
    /// * `binders`: an iterator over the telescope's binders in source order (although it must be
    ///   reversible as the binders will be used in the reverse of this order)
    /// * `body`: the body of the lambda.
    /// * `span`: The source span which will be used for all lambda terms in the output
    ///
    /// # Panics
    /// If the [`ty`] field of any element of `binders` is not a type.
    ///
    /// [`ty`]: TypedBinder::ty
    pub fn make_lambda_telescope(
        binders: impl IntoIterator<IntoIter: DoubleEndedIterator<Item = TypedBinder>>,
        body: TypedTerm,
        span: Span,
    ) -> TypedTerm {
        binders.into_iter().rfold(body, |acc, binder| {
            TypedTerm::make_lambda(binder, acc, span.clone())
        })
    }
}

impl TypedTermKind {
    /// Constructs a term representing the sort literal `Sort <level>`
    pub fn sort_literal(level: Level) -> Rc<Self> {
        let properties = CachedTermProperties::sort_literal(&level);

        Self::from_parts(TypedTermKindInner::SortLiteral(level), properties, None)
    }

    /// Constructs a term referring to the name of an ADT
    pub fn adt_name(adt: AdtIndex, level_args: LevelArgs) -> Rc<Self> {
        let properties = CachedTermProperties::adt_constant(&level_args);

        Self::from_parts(
            TypedTermKindInner::AdtName(adt, level_args),
            properties,
            None,
        )
    }

    /// Constructs a term referring to a constructor of an ADT
    pub fn adt_constructor(adt: AdtIndex, constructor: usize, level_args: LevelArgs) -> Rc<Self> {
        let properties = CachedTermProperties::adt_constant(&level_args);

        Self::from_parts(
            TypedTermKindInner::AdtConstructor(adt, constructor, level_args),
            properties,
            None,
        )
    }

    /// Constructs a term referring to the recursor of an ADT
    pub fn adt_recursor(adt: AdtIndex, level_args: LevelArgs) -> Rc<Self> {
        let properties = CachedTermProperties::adt_constant(&level_args);

        Self::from_parts(
            TypedTermKindInner::AdtRecursor(adt, level_args),
            properties,
            None,
        )
    }

    /// Constructs a term referring to an axiom
    pub fn axiom(axiom_index: AxiomIndex, level_args: LevelArgs) -> Rc<Self> {
        let properties = CachedTermProperties::adt_constant(&level_args);

        Self::from_parts(
            TypedTermKindInner::Axiom(axiom_index, level_args),
            properties,
            None,
        )
    }

    /// Constructs a term referring to a bound variable.
    pub fn bound_variable(index: usize, name: Option<Identifier>) -> Rc<Self> {
        Self::from_parts(
            TypedTermKindInner::BoundVariable { index, name },
            CachedTermProperties::bound_variable(index),
            None,
        )
    }

    /// Constructs a term referring to an application of a function to an argument
    pub fn application(function: TypedTerm, argument: TypedTerm) -> Rc<Self> {
        let properties = CachedTermProperties::application(&function, &argument);

        Self::from_parts(
            TypedTermKindInner::Application { function, argument },
            properties,
            None,
        )
    }

    /// Constructs a term referring to a pi type with the given binder and output
    pub fn pi_type(binder: TypedBinder, output: TypedTerm) -> Rc<Self> {
        let properties = CachedTermProperties::combine_binder_with_term(&binder, &output);

        Self::from_parts(
            TypedTermKindInner::PiType { binder, output },
            properties,
            None,
        )
    }

    /// Constructs a term referring to a lambda abstraction with the given binder and body
    pub fn lambda(binder: TypedBinder, body: TypedTerm) -> Rc<Self> {
        let properties = CachedTermProperties::combine_binder_with_term(&binder, &body);

        Self::from_parts(
            TypedTermKindInner::Lambda { binder, body },
            properties,
            None,
        )
    }

    /// Constructs a [`TypedTermKind`] from its constituent parts, wrapping it in an [`Rc`].
    pub(super) fn from_parts(
        inner: TypedTermKindInner,
        cached_properties: CachedTermProperties,
        abbreviation: Option<Rc<Abbreviation>>,
    ) -> Rc<Self> {
        Rc::new(Self {
            cached_properties,
            inner,
            abbreviation,
        })
    }
}

impl CachedTermProperties {
    /// Computes the cached properties for a term which refers to a constant of an ADT (either the
    /// ADT's name, a constructor, or the recursor)
    fn adt_constant(level_args: &LevelArgs) -> Self {
        Self {
            checked: Cell::new(false),
            indices_less_than: 0,
            mentions_level_parameter: level_args.mentions_parameters(),
        }
    }

    /// Computes the cached properties for a sort literal term
    fn sort_literal(level: &Level) -> Self {
        Self {
            checked: Cell::new(false),
            indices_less_than: 0,
            mentions_level_parameter: level.mentions_parameters(),
        }
    }

    /// Computes the cached properties for a bound variable term
    fn bound_variable(index: usize) -> Self {
        Self {
            checked: Cell::new(false),
            indices_less_than: index + 1,
            mentions_level_parameter: false,
        }
    }

    /// Computes the union of the cached properties of two [`TypedTermKind`]s. The cached
    /// properties will be the laxer of the properties from the inputs.
    fn union(&self, other: &Self) -> Self {
        Self {
            checked: Cell::new(false),
            indices_less_than: self.indices_less_than.max(other.indices_less_than),
            mentions_level_parameter: self.mentions_level_parameter
                || other.mentions_level_parameter,
        }
    }

    /// Computes the cached properties for an application of a function to an argument
    fn application(a: &TypedTerm, b: &TypedTerm) -> Self {
        a.term
            .cached_properties
            .union(&a.ty.cached_properties)
            .union(&b.term.cached_properties)
            .union(&b.ty.cached_properties)
    }

    /// Decreases [`indices_less_than`] by one
    ///
    /// [`indices_less_than`]: CachedTermProperties::indices_less_than
    fn decrement_indices(&self) -> Self {
        Self {
            indices_less_than: self.indices_less_than.saturating_sub(1),
            ..self.clone()
        }
    }

    /// Computes the cached properties for a pi type or lambda abstraction, where `b` is the binder
    /// and `t` is the term directly under that binder
    fn combine_binder_with_term(b: &TypedBinder, t: &TypedTerm) -> Self {
        b.ty.term
            .cached_properties
            .union(&b.ty.ty.cached_properties)
            .union(&t.term.cached_properties.decrement_indices())
            .union(&t.ty.cached_properties.decrement_indices())
    }
}
