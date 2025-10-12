use crate::parser::atoms::ident::Identifier;
use crate::typeck::level::{Level, LevelArgs};
use crate::typeck::term::{TypedBinder, TypedTerm, TypedTermKind, TypedTermKindInner};
use crate::typeck::{AdtIndex, TypeError};

impl TypedTerm {
    pub fn level(&self) -> Level {
        self.level.clone()
    }

    pub fn ty(&self) -> TypedTermKind {
        self.ty.clone()
    }

    pub fn term(&self) -> TypedTermKind {
        self.term.clone()
    }

    /// Checks that the term represents a type. If it is, returns what level it is in.
    pub fn check_is_ty(&self) -> Result<Level, TypeError> {
        self.ty()
            .check_is_sort()
            .map_err(|_| TypeError::NotAType(self.clone()))
    }

    pub fn get_type(&self) -> TypedTerm {
        TypedTerm {
            level: self.level.succ(),
            ty: TypedTermKind::sort_literal(self.level.clone()),
            term: self.ty.clone(),
        }
    }

    pub fn is_sort_literal(&self) -> Option<Level> {
        match self.term().inner() {
            TypedTermKindInner::SortLiteral(l) => Some(l.clone()),
            _ => None,
        }
    }

    pub fn is_bound_variable(&self) -> Option<(usize, Option<Identifier>)> {
        match self.term().inner() {
            TypedTermKindInner::BoundVariable { index, name } => Some((*index, *name)),
            _ => None,
        }
    }

    pub fn is_adt_name(&self) -> Option<(AdtIndex, LevelArgs)> {
        match self.term().inner() {
            TypedTermKindInner::AdtName(adt, level_args) => Some((*adt, level_args.clone())),
            _ => None,
        }
    }

    pub fn is_adt_constructor(&self) -> Option<(AdtIndex, usize, LevelArgs)> {
        match self.term().inner() {
            TypedTermKindInner::AdtConstructor(adt, index, level_args) => {
                Some((*adt, *index, level_args.clone()))
            }
            _ => None,
        }
    }

    pub fn is_pi_type(&self) -> Option<(TypedBinder, TypedTerm)> {
        match self.term().inner() {
            TypedTermKindInner::PiType { binder, output } => Some((binder.clone(), output.clone())),
            _ => None,
        }
    }

    pub fn is_application(&self) -> Option<(TypedTerm, TypedTerm)> {
        match self.term().inner() {
            TypedTermKindInner::Application { function, argument } => {
                Some((function.clone(), argument.clone()))
            }
            _ => None,
        }
    }

    pub fn is_lambda(&self) -> Option<(TypedBinder, TypedTerm)> {
        match self.term().inner() {
            TypedTermKindInner::Lambda { binder, body } => Some((binder.clone(), body.clone())),
            _ => None,
        }
    }

    /// Decomposes a term as a telescope of pi types, returning the binders and the final output
    pub fn decompose_telescope(mut self) -> (Vec<TypedBinder>, TypedTerm) {
        let mut indices = Vec::new();

        loop {
            if let Some((binder, output)) = self.is_pi_type() {
                indices.push(binder);
                self = output;
            } else {
                break;
            }
        }

        (indices, self)
    }

    /// Decomposes a term as a stack of function applications, returning the underlying function and the arguments.
    /// Arguments are returned in the reverse of their source order.
    pub fn decompose_application_stack_reversed(&self) -> (TypedTerm, Vec<TypedTerm>) {
        let mut args = Vec::new();

        let mut s = self.clone();

        loop {
            if let Some((function, argument)) = s.is_application() {
                args.push(argument);
                s = function;
            } else {
                break;
            }
        }

        (s, args)
    }

    /// Decomposes a term as a stack of function applications, returning the underlying function and the arguments.
    /// Arguments are returned in their source order.
    pub fn decompose_application_stack(&self) -> (TypedTerm, Vec<TypedTerm>) {
        let (s, mut args) = self.decompose_application_stack_reversed();

        args.reverse();
        (s, args)
    }
}

impl TypedTermKind {
    /// Checks that the term is a sort literal, returning its level
    pub fn check_is_sort(&self) -> Result<Level, ()> {
        match self.inner() {
            TypedTermKindInner::SortLiteral(u) => Ok(u.clone()),
            _ => Err(()),
        }
    }

    pub fn references_bound_variable(&self, id: usize) -> bool {
        use TypedTermKindInner::*;

        match self.inner() {
            SortLiteral(_) | AdtName(_, _) | AdtConstructor(_, _, _) | AdtRecursor(_, _) => false,

            BoundVariable { index, name } => *index == id,
            Application { function, argument } => {
                function.term.references_bound_variable(id)
                    || argument.term.references_bound_variable(id)
            }
            PiType { binder, output } => {
                binder.ty.term.references_bound_variable(id)
                    || output.term.references_bound_variable(id + 1)
            }
            Lambda { binder, body } => {
                binder.ty.term.references_bound_variable(id)
                    || body.term.references_bound_variable(id + 1)
            }
        }
    }

    /// Checks that a term does not reference a given ADT. This is only used while type-checking the
    /// definition of the ADT in question, so it can be assumed that [`DefinedConstant`]s do not
    /// reference the ADT.
    ///
    /// [`DefinedConstant`]: TypedTermKindInner::DefinedConstant
    pub fn forbid_references_to_adt(&self, adt: AdtIndex) -> Result<(), TypeError> {
        use TypedTermKindInner::*;

        match self.inner() {
            AdtName(id, _) | AdtConstructor(id, _, _) | AdtRecursor(id, _) if *id == adt => {
                Err(TypeError::InvalidLocationForAdtNameInConstructor(adt))
            }
            AdtName(_, _) | AdtConstructor(_, _, _) | AdtRecursor(_, _) => Ok(()),

            SortLiteral(_) | BoundVariable { .. } => Ok(()),

            Application { function, argument } => {
                function.term.forbid_references_to_adt(adt)?;
                argument.term.forbid_references_to_adt(adt)
            }
            PiType { binder, output } => {
                binder.ty.term.forbid_references_to_adt(adt)?;
                output.term.forbid_references_to_adt(adt)
            }
            Lambda { binder, body } => {
                binder.ty.term.forbid_references_to_adt(adt)?;
                body.term.forbid_references_to_adt(adt)
            }
        }
    }
}
