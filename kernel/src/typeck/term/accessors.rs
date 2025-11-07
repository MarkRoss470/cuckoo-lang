//! Methods to query and destructure [`TypedTerm`], [`TypedTermKind`], and [`TypedBinder`] instances

use crate::typeck::error::TypeErrorKind;
use crate::typeck::level::{Level, LevelArgs};
use crate::typeck::term::{TypedBinder, TypedTerm, TypedTermKind, TypedTermKindInner};
use crate::typeck::{AdtIndex, TypeError};
use parser::error::Span;
use std::rc::Rc;

impl TypedTerm {
    /// Gets the source span of the term
    pub fn span(&self) -> Span {
        self.span.clone()
    }

    /// Gets the universe level of the term
    pub fn level(&self) -> Level {
        self.level.clone()
    }

    /// Gets the [kind] of the term's type
    ///
    /// [kind]: TypedTermKind
    pub fn ty(&self) -> Rc<TypedTermKind> {
        self.ty.clone()
    }

    /// Gets the [kind] of the term
    ///
    /// [kind]: TypedTermKind
    pub fn term(&self) -> Rc<TypedTermKind> {
        self.term.clone()
    }

    /// Checks that the term represents a type. If it is, returns what level it is in.
    /// If not, returns a [`NotAType`] error.
    ///
    /// [`NotAType`]: TypeErrorKind::NotAType
    pub fn check_is_ty(&self) -> Result<Level, TypeError> {
        // The term represents a type if its type is a sort literal
        self.ty().check_is_sort().map_err(|_| TypeError {
            span: self.span(),
            kind: TypeErrorKind::NotAType(self.clone()),
        })
    }

    /// Gets the type of the term as another [`TypedTerm`]
    pub fn get_type(&self) -> TypedTerm {
        TypedTerm {
            span: self.span(),
            level: self.level.succ(),
            ty: TypedTermKind::sort_literal(self.level.clone()),
            term: self.ty.clone(),
        }
    }

    /// Checks whether the term refers to a sort. If it does, returns the level of the sort.
    pub fn is_sort_literal(&self) -> Option<Level> {
        match self.term().inner() {
            TypedTermKindInner::SortLiteral(l) => Some(l.clone()),
            _ => None,
        }
    }

    /// Checks whether the term refers to an ADT name. If it does, returns the ADT
    /// and the level arguments given to it.
    pub fn is_adt_name(&self) -> Option<(AdtIndex, LevelArgs)> {
        match self.term().inner() {
            TypedTermKindInner::AdtName(adt, level_args) => Some((*adt, level_args.clone())),
            _ => None,
        }
    }

    /// Checks whether the term refers to a constructor of an ADT. If it does, returns the ADT,
    /// the constructor's index, and the level arguments given to it.
    pub fn is_adt_constructor(&self) -> Option<(AdtIndex, usize, LevelArgs)> {
        match self.term().inner() {
            TypedTermKindInner::AdtConstructor(adt, index, level_args) => {
                Some((*adt, *index, level_args.clone()))
            }
            _ => None,
        }
    }

    /// Checks whether the term refers to a pi type. If it does, returns the binder and return type
    /// of the pi type.
    pub fn is_pi_type(&self) -> Option<(TypedBinder, TypedTerm)> {
        match self.term().inner() {
            TypedTermKindInner::PiType { binder, output } => Some((binder.clone(), output.clone())),
            _ => None,
        }
    }

    /// Checks whether the term refers to an application of a function to an argument.
    /// If it does, returns the function and argument.
    pub fn is_application(&self) -> Option<(TypedTerm, TypedTerm)> {
        match self.term().inner() {
            TypedTermKindInner::Application { function, argument } => {
                Some((function.clone(), argument.clone()))
            }
            _ => None,
        }
    }

    /// Checks whether the term refers to a lambda abstraction. If it does, returns the binder and
    /// body of the lambda abstraction.
    pub fn is_lambda(&self) -> Option<(TypedBinder, TypedTerm)> {
        match self.term().inner() {
            TypedTermKindInner::Lambda { binder, body } => Some((binder.clone(), body.clone())),
            _ => None,
        }
    }

    /// Decomposes a term as a telescope of pi types, returning the binders in source order
    /// and the output type.
    pub fn decompose_telescope(mut self) -> (Vec<TypedBinder>, TypedTerm) {
        let mut indices = Vec::new();

        while let Some((binder, output)) = self.is_pi_type() {
            indices.push(binder);
            self = output;
        }

        (indices, self)
    }

    /// Decomposes a term as a stack of function applications, returning the underlying function
    /// and the arguments in reverse source order.
    pub fn decompose_application_stack_reversed(&self) -> (TypedTerm, Vec<TypedTerm>) {
        let mut args = Vec::new();
        let mut s = self.clone();

        while let Some((function, argument)) = s.is_application() {
            args.push(argument);
            s = function;
        }

        (s, args)
    }

    /// Decomposes a term as a stack of function applications, returning the underlying function
    /// and the arguments in source order.
    pub fn decompose_application_stack(&self) -> (TypedTerm, Vec<TypedTerm>) {
        let (s, mut args) = self.decompose_application_stack_reversed();

        args.reverse();
        (s, args)
    }

    /// Checks that a term does not reference a given ADT.
    /// If the ADT is referenced, returns an [`InvalidLocationForAdtNameInConstructor`] error.
    ///
    /// This is only used while type-checking the
    /// definition of the ADT in question, so it can be assumed that [`Axiom`]s do not
    /// reference the ADT.
    ///
    /// [`InvalidLocationForAdtNameInConstructor`]: TypeErrorKind::InvalidLocationForAdtNameInConstructor
    /// [`Axiom`]: TypedTermKindInner::Axiom
    pub fn forbid_references_to_adt(&self, adt: AdtIndex) -> Result<(), TypeError> {
        self.term.forbid_references_to_adt(adt, self.span())?;
        self.ty.forbid_references_to_adt(adt, self.span())
    }
}

impl TypedTermKind {
    /// Gets a reference to the contained [`TypedTermKindInner`]
    pub(super) fn inner(&self) -> &TypedTermKindInner {
        &self.inner
    }

    /// Clones the contained [`TypedTermKindInner`]
    pub(super) fn clone_inner(&self) -> TypedTermKindInner {
        self.inner.clone()
    }

    /// Checks that the term is a sort literal, returning its level
    pub fn check_is_sort(&self) -> Result<Level, ()> {
        match self.inner() {
            TypedTermKindInner::SortLiteral(u) => Ok(u.clone()),
            _ => Err(()),
        }
    }

    /// Checks that a term does not reference a given ADT.
    /// If the ADT is referenced, returns an [`InvalidLocationForAdtNameInConstructor`] error.
    ///
    /// This is only used while type-checking the
    /// definition of the ADT in question, so it can be assumed that [`Axiom`]s do not
    /// reference the ADT.
    ///
    /// [`InvalidLocationForAdtNameInConstructor`]: TypeErrorKind::InvalidLocationForAdtNameInConstructor
    /// [`Axiom`]: TypedTermKindInner::Axiom
    fn forbid_references_to_adt(&self, adt: AdtIndex, span: Span) -> Result<(), TypeError> {
        use TypedTermKindInner::*;

        match self.inner() {
            AdtName(id, _) | AdtConstructor(id, _, _) | AdtRecursor(id, _) if *id == adt => {
                Err(TypeError {
                    span,
                    kind: TypeErrorKind::InvalidLocationForAdtNameInConstructor(adt),
                })
            }
            AdtName(_, _) | AdtConstructor(_, _, _) | AdtRecursor(_, _) | Axiom(_, _) => Ok(()),

            SortLiteral(_) | BoundVariable { .. } => Ok(()),

            Application { function, argument } => {
                function.forbid_references_to_adt(adt)?;
                argument.forbid_references_to_adt(adt)
            }
            PiType { binder, output } => {
                binder.ty.forbid_references_to_adt(adt)?;
                output.forbid_references_to_adt(adt)
            }
            Lambda { binder, body } => {
                binder.ty.forbid_references_to_adt(adt)?;
                body.forbid_references_to_adt(adt)
            }
        }
    }
}

impl TypedBinder {
    /// Gets the source span of the binder
    pub fn span(&self) -> Span {
        self.span.clone()
    }

    /// Gets the universe level of the binder's type
    pub fn level(&self) -> Level {
        self.ty.check_is_ty().unwrap()
    }
}
