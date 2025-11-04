use crate::typeck::level::LevelArgs;
use crate::typeck::term::{
    Abbreviation, TypedBinder, TypedTerm, TypedTermKind, TypedTermKindInner,
};
use std::rc::Rc;

impl TypedTerm {
    /// Replaces the binder with de Bruijn index `id` with the given term, adding `id` to the ids of all bound variables in the new expression
    pub fn replace_binder(&self, id: usize, expr: &TypedTerm) -> Self {
        Self {
            span: self.span(),
            level: self.level(),
            ty: self.ty.replace_binder(id, expr),
            term: self.term.replace_binder(id, expr),
        }
    }

    pub fn instantiate(&self, level_args: &LevelArgs) -> Self {
        Self {
            span: self.span(),
            level: self.level().instantiate_parameters(level_args),
            ty: self.ty.instantiate(level_args),
            term: self.term.instantiate(level_args),
        }
    }

    /// Clones the value, while incrementing all bound variable indices by `inc`
    pub fn increment_above(&self, limit: usize, inc: usize) -> Self {
        Self {
            span: self.span(),
            level: self.level(),
            ty: self.ty.increment_above(limit, inc),
            term: self.term.increment_above(limit, inc),
        }
    }

    pub fn with_abbreviation(self, abbreviation: Abbreviation) -> Self {
        Self {
            term: self.term.with_abbreviation(abbreviation),
            ..self
        }
    }

    pub fn with_abbreviation_from(self, other: &Self) -> Self {
        Self {
            term: self.term.with_abbreviation_from(&other.term),
            ..self
        }
    }

    pub fn clear_abbreviation(self) -> Self {
        Self {
            term: self.term.with_potential_abbreviation(None),
            ..self
        }
    }

    pub fn normalize_level(self) -> Self {
        Self {
            level: self.level.normalize(),
            ..self
        }
    }
}

impl TypedTermKind {
    #[must_use]
    pub(super) fn instantiate(self: &Rc<Self>, level_args: &LevelArgs) -> Rc<Self> {
        use TypedTermKindInner::*;

        // If the term doesn't reference any level parameters, instantiating it won't change it
        if !self.cached_properties.mentions_level_parameter {
            return self.clone();
        }

        let new = match self.inner() {
            SortLiteral(l) => Self::sort_literal(l.instantiate_parameters(level_args)),
            AdtName(adt, args) => Self::adt_name(*adt, args.instantiate_parameters(level_args)),
            AdtConstructor(adt, constructor, args) => {
                Self::adt_constructor(*adt, *constructor, args.instantiate_parameters(level_args))
            }
            AdtRecursor(adt, args) => {
                Self::adt_recursor(*adt, args.instantiate_parameters(level_args))
            }
            Axiom(axiom, args) => Self::axiom(*axiom, args.instantiate_parameters(level_args)),
            BoundVariable { .. } => self.clone(),
            Application { function, argument } => Self::application(
                function.instantiate(level_args),
                argument.instantiate(level_args),
            ),
            PiType { binder, output } => Self::pi_type(
                binder.instantiate(level_args),
                output.instantiate(level_args),
            ),
            Lambda { binder, body } => {
                Self::lambda(binder.instantiate(level_args), body.instantiate(level_args))
            }
        };

        // If instantiation didn't change anything, return `self`
        if self.equiv(&new, true) {
            self.clone()
        } else {
            new.with_potential_abbreviation(
                self.abbreviation
                    .as_ref()
                    .map(|a| a.instantiate(level_args)),
            )
        }
    }

    /// Clones the value, while incrementing all bound variable indices above `limit` by `inc`
    #[must_use]
    pub fn increment_above(self: &Rc<Self>, limit: usize, inc: usize) -> Rc<Self> {
        use TypedTermKindInner::*;

        // If the term definitely doesn't reference any variables above `limit`, just return it.
        if self.cached_properties.indices_less_than <= limit {
            return self.clone();
        }

        let new = match self.inner() {
            AdtName(_, _)
            | SortLiteral(_)
            | AdtConstructor(_, _, _)
            | AdtRecursor(_, _)
            | Axiom(_, _) => return self.clone(),
            BoundVariable { index, .. } if *index < limit => return self.clone(),
            BoundVariable { index, name } => Self::bound_variable(index + inc, *name),
            Application { function, argument } => Self::application(
                function.increment_above(limit, inc),
                argument.increment_above(limit, inc),
            ),
            PiType { binder, output } => Self::pi_type(
                binder.increment_above(limit, inc),
                output.increment_above(limit + 1, inc),
            ),
            Lambda { binder, body } => Self::lambda(
                binder.increment_above(limit, inc),
                body.increment_above(limit + 1, inc),
            ),
        };

        // If incrementing didn't change anything, return `self`
        if self.equiv(&new, true) {
            self.clone()
        } else {
            new.with_potential_abbreviation(
                self.abbreviation
                    .as_ref()
                    .map(|a| a.increment_above(limit, inc)),
            )
        }
    }

    /// Replaces the binder with de Bruijn index `id` with the given term, adding `id` to the ids of all bound variables in the substituted term
    #[must_use]
    pub(super) fn replace_binder(self: &Rc<Self>, id: usize, expr: &TypedTerm) -> Rc<Self> {
        use TypedTermKindInner::*;

        // If the term definitely doesn't reference the variable, just return it.
        if self.cached_properties.indices_less_than <= id {
            return self.clone();
        }

        let new = match self.inner() {
            SortLiteral(_)
            | AdtName(_, _)
            | AdtConstructor(_, _, _)
            | AdtRecursor(_, _)
            | Axiom(_, _) => return self.clone(),
            // Bound variables with index less than `id` are unaffected
            BoundVariable { index, .. } if *index < id => return self.clone(),
            // References to bound variable `id` are replaced with `expr`
            BoundVariable { index, .. } if *index == id => expr.term.increment_above(0, id),
            // Bound variables greater than `id` are decreased by one because binder `id` has been removed.
            BoundVariable { index, name } => Self::bound_variable(index - 1, *name),
            Application { function, argument } => Self::application(
                function.replace_binder(id, expr),
                argument.replace_binder(id, expr),
            ),
            PiType { binder, output } => Self::pi_type(
                binder.replace_binder(id, expr),
                output.replace_binder(id + 1, expr),
            ),
            Lambda { binder, body } => Self::lambda(
                binder.replace_binder(id, expr),
                body.replace_binder(id + 1, expr),
            ),
        };

        // If replacing the binder didn't change anything, return `self`
        if self.equiv(&new, true) {
            self.clone()
        } else {
            new.with_potential_abbreviation(
                self.abbreviation
                    .as_ref()
                    .map(|a| a.replace_binder(id, expr)),
            )
        }
    }

    pub fn with_potential_abbreviation(&self, abbreviation: Option<Rc<Abbreviation>>) -> Rc<Self> {
        Rc::new(Self {
            abbreviation,
            ..self.clone()
        })
    }

    pub fn with_abbreviation(&self, abbreviation: Abbreviation) -> Rc<Self> {
        self.with_potential_abbreviation(Some(Rc::new(abbreviation)))
    }

    pub fn with_abbreviation_from(&self, other: &Self) -> Rc<Self> {
        self.with_potential_abbreviation(other.abbreviation.clone())
    }

    pub fn clear_abbreviation(&self) -> Rc<Self> {
        self.with_potential_abbreviation(None)
    }
}

impl Abbreviation {
    fn instantiate(self: &Rc<Self>, level_args: &LevelArgs) -> Rc<Self> {
        match self.as_ref() {
            Abbreviation::Constant(path, args) => Rc::new(Self::Constant(
                path.clone(),
                args.instantiate_parameters(level_args),
            )),
            Abbreviation::Application(abbr, term) => Rc::new(Self::Application(
                abbr.instantiate(level_args),
                term.instantiate(level_args),
            )),
        }
    }

    fn increment_above(self: &Rc<Self>, limit: usize, inc: usize) -> Rc<Self> {
        match self.as_ref() {
            Abbreviation::Constant(_, _) => self.clone(),
            Abbreviation::Application(abbr, term) => Rc::new(Self::Application(
                abbr.increment_above(limit, inc),
                term.increment_above(limit, inc),
            )),
        }
    }

    fn replace_binder(self: &Rc<Self>, id: usize, expr: &TypedTerm) -> Rc<Self> {
        match self.as_ref() {
            Abbreviation::Constant(_, _) => self.clone(),
            Abbreviation::Application(abbr, term) => Rc::new(Self::Application(
                abbr.replace_binder(id, expr),
                term.replace_binder(id, expr),
            )),
        }
    }
}

impl TypedBinder {
    /// Replaces the binder with de Bruijn index `id` with the given term
    #[must_use]
    pub(super) fn replace_binder(&self, id: usize, expr: &TypedTerm) -> Self {
        Self {
            span: self.span(),
            name: self.name,
            ty: self.ty.replace_binder(id, expr),
        }
    }

    #[must_use]
    pub(super) fn instantiate(&self, level_args: &LevelArgs) -> Self {
        Self {
            span: self.span(),
            name: self.name,
            ty: self.ty.instantiate(level_args),
        }
    }

    /// Clones the value, while incrementing all bound variable indices by `inc`
    #[must_use]
    fn increment_above(&self, limit: usize, inc: usize) -> Self {
        Self {
            span: self.span(),
            name: self.name,
            ty: self.ty.increment_above(limit, inc),
        }
    }
}
