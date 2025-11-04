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
    pub(crate) fn value_of_type(value: Rc<TypedTermKind>, ty: TypedTerm, span: Span) -> TypedTerm {
        TypedTerm {
            span,
            level: ty.check_is_ty().expect("`ty` should have been a type"),
            ty: ty.term.clone(),
            term: value,
        }
    }

    pub fn sort_literal(level: Level, span: Span) -> TypedTerm {
        TypedTerm {
            span,
            level: level.succ().succ(),
            ty: TypedTermKind::sort_literal(level.succ()),
            term: TypedTermKind::sort_literal(level),
        }
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

    pub fn adt_name(
        adt_index: AdtIndex,
        ty: TypedTerm,
        level_args: LevelArgs,
        span: Span,
    ) -> TypedTerm {
        TypedTerm::value_of_type(TypedTermKind::adt_name(adt_index, level_args), ty, span)
    }

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

    pub fn adt_recursor(
        adt_index: AdtIndex,
        ty: TypedTerm,
        level_args: LevelArgs,
        span: Span,
    ) -> TypedTerm {
        TypedTerm::value_of_type(TypedTermKind::adt_recursor(adt_index, level_args), ty, span)
    }

    pub fn axiom(
        axiom_index: AxiomIndex,
        ty: TypedTerm,
        level_args: LevelArgs,
        span: Span,
    ) -> TypedTerm {
        TypedTerm::value_of_type(TypedTermKind::axiom(axiom_index, level_args), ty, span)
    }

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

    pub fn make_application(
        function: TypedTerm,
        argument: TypedTerm,
        output: TypedTerm,
        span: Span,
    ) -> TypedTerm {
        TypedTerm::value_of_type(TypedTermKind::application(function, argument), output, span)
    }

    pub fn make_lambda(binder: TypedBinder, body: TypedTerm, span: Span) -> TypedTerm {
        TypedTerm::value_of_type(
            TypedTermKind::lambda(binder.clone(), body.clone()),
            TypedTerm::make_pi_type(binder, body.get_type(), span.clone()),
            span,
        )
    }

    pub fn make_telescope(
        binders: impl IntoIterator<IntoIter: DoubleEndedIterator<Item = TypedBinder>>,
        output: TypedTerm,
        span: Span,
    ) -> TypedTerm {
        binders.into_iter().rfold(output, |acc, binder| {
            TypedTerm::make_pi_type(binder, acc, span.clone())
        })
    }

    pub fn make_application_stack(
        function: TypedTerm,
        params: impl IntoIterator<Item = Rc<TypedTermKind>>,
        span: Span,
    ) -> TypedTerm {
        let mut res = function;

        for param in params {
            let TypedTermKindInner::PiType { binder, output } = res.ty.clone_inner() else {
                panic!("`res` should have been a function type")
            };

            let param = TypedTerm::value_of_type(param, binder.ty, span.clone());
            let output = output.replace_binder(0, &param);
            res = TypedTerm::make_application(res, param, output, span.clone());
        }

        res
    }

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
    pub fn sort_literal(level: Level) -> Rc<Self> {
        let properties = CachedTermProperties::sort_literal(&level);

        Self::from_inner(TypedTermKindInner::SortLiteral(level), properties, None)
    }

    pub fn adt_name(adt: AdtIndex, level_args: LevelArgs) -> Rc<Self> {
        let properties = CachedTermProperties::path(&level_args);

        Self::from_inner(
            TypedTermKindInner::AdtName(adt, level_args),
            properties,
            None,
        )
    }

    pub fn adt_constructor(adt: AdtIndex, constructor: usize, level_args: LevelArgs) -> Rc<Self> {
        let properties = CachedTermProperties::path(&level_args);

        Self::from_inner(
            TypedTermKindInner::AdtConstructor(adt, constructor, level_args),
            properties,
            None,
        )
    }

    pub fn adt_recursor(adt: AdtIndex, level_args: LevelArgs) -> Rc<Self> {
        let properties = CachedTermProperties::path(&level_args);

        Self::from_inner(
            TypedTermKindInner::AdtRecursor(adt, level_args),
            properties,
            None,
        )
    }

    pub fn axiom(axiom_index: AxiomIndex, level_args: LevelArgs) -> Rc<Self> {
        let properties = CachedTermProperties::path(&level_args);

        Self::from_inner(
            TypedTermKindInner::Axiom(axiom_index, level_args),
            properties,
            None,
        )
    }

    pub fn bound_variable(index: usize, name: Option<Identifier>) -> Rc<Self> {
        Self::from_inner(
            TypedTermKindInner::BoundVariable { index, name },
            CachedTermProperties::bound_variable(index),
            None,
        )
    }

    pub fn application(function: TypedTerm, argument: TypedTerm) -> Rc<Self> {
        let properties = CachedTermProperties::combine_terms(&function, &argument);

        Self::from_inner(
            TypedTermKindInner::Application { function, argument },
            properties,
            None,
        )
    }

    pub fn pi_type(binder: TypedBinder, output: TypedTerm) -> Rc<Self> {
        let properties = CachedTermProperties::combine_terms(&binder.ty, &output);

        Self::from_inner(
            TypedTermKindInner::PiType { binder, output },
            properties,
            None,
        )
    }

    pub fn lambda(binder: TypedBinder, body: TypedTerm) -> Rc<Self> {
        let properties = CachedTermProperties::combine_terms(&binder.ty, &body);

        Self::from_inner(
            TypedTermKindInner::Lambda { binder, body },
            properties,
            None,
        )
    }

    pub(super) fn from_inner(
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

impl TypedBinder {
    pub fn level(&self) -> Level {
        self.ty.check_is_ty().unwrap()
    }
}

impl CachedTermProperties {
    fn path(level_args: &LevelArgs) -> Self {
        Self {
            checked: Cell::new(false),
            indices_less_than: 0,
            mentions_level_parameter: level_args.mentions_parameters(),
        }
    }

    fn sort_literal(level: &Level) -> Self {
        Self {
            checked: Cell::new(false),
            indices_less_than: 0,
            mentions_level_parameter: level.mentions_parameters(),
        }
    }

    fn bound_variable(index: usize) -> Self {
        Self {
            checked: Cell::new(false),
            indices_less_than: index + 1,
            mentions_level_parameter: false,
        }
    }

    fn union(&self, other: &Self) -> Self {
        Self {
            checked: Cell::new(false),
            indices_less_than: self.indices_less_than.max(other.indices_less_than),
            mentions_level_parameter: self.mentions_level_parameter
                || other.mentions_level_parameter,
        }
    }

    fn combine_terms(a: &TypedTerm, b: &TypedTerm) -> Self {
        a.term
            .cached_properties
            .union(&a.ty.cached_properties)
            .union(&b.term.cached_properties)
            .union(&b.ty.cached_properties)
    }
}
