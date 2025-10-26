use crate::typeck::level::LevelArgs;
use crate::typeck::term::{
    Abbreviation, TypedBinder, TypedTerm, TypedTermKind, TypedTermKindInner,
};
use std::cell::Cell;
use std::rc::Rc;

impl TypedTerm {
    /// Replaces the binder with de Bruijn index `id` with the given term, adding `id` to the ids of all bound variables in the new expression
    pub fn replace_binder(&self, id: usize, expr: &TypedTerm) -> Self {
        Self {
            checked: Cell::new(false),
            span: self.span(),
            level: self.level(),
            ty: self.ty.replace_binder(id, expr),
            term: self.term.replace_binder(id, expr),
        }
    }

    pub fn instantiate(&self, level_args: &LevelArgs) -> Self {
        Self {
            checked: Cell::new(false),
            span: self.span(),
            level: self.level().instantiate_parameters(level_args),
            ty: self.ty.instantiate(level_args),
            term: self.term.instantiate(level_args),
        }
    }

    /// Clones the value, while incrementing all bound variable indices by `inc`
    pub fn clone_incrementing(&self, limit: usize, inc: usize) -> Self {
        Self {
            checked: Cell::new(false),
            span: self.span(),
            level: self.level(),
            ty: self.ty.clone_incrementing(limit, inc),
            term: self.term.clone_incrementing(limit, inc),
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

        let inner = match self.inner() {
            SortLiteral(l) => SortLiteral(l.instantiate_parameters(level_args)),

            AdtName(adt, args) => AdtName(*adt, args.instantiate_parameters(level_args)),
            AdtConstructor(adt, constructor, args) => {
                AdtConstructor(*adt, *constructor, args.instantiate_parameters(level_args))
            }
            AdtRecursor(adt, args) => AdtRecursor(*adt, args.instantiate_parameters(level_args)),
            Axiom(axiom, args) => Axiom(*axiom, args.instantiate_parameters(level_args)),
            BoundVariable { index: _, name: _ } => {
                return self.clone();
            }

            Application { function, argument } => Application {
                function: function.instantiate(level_args),
                argument: argument.instantiate(level_args),
            },
            PiType { binder, output } => PiType {
                binder: binder.instantiate(level_args),
                output: output.instantiate(level_args),
            },
            Lambda { binder, body } => Lambda {
                binder: binder.instantiate(level_args),
                body: body.instantiate(level_args),
            },
        };

        Self::from_inner(
            inner,
            self.abbreviation
                .as_ref()
                .map(|abbr| abbr.instantiate(level_args)),
        )
    }

    // TODO: rename as cloning is no longer special
    /// Clones the value, while incrementing all bound variable indices above `limit` by `inc`
    #[must_use]
    pub fn clone_incrementing(self: &Rc<Self>, limit: usize, inc: usize) -> Rc<Self> {
        use TypedTermKindInner::*;

        let inner = match self.inner() {
            inner @ (AdtName(_, _)
            | SortLiteral(_)
            | AdtConstructor(_, _, _)
            | AdtRecursor(_, _)
            | Axiom(_, _)) => inner.clone(),
            BoundVariable { index, name } => BoundVariable {
                index: if *index >= limit { index + inc } else { *index },
                name: *name,
            },
            Application { function, argument } => Application {
                function: function.clone_incrementing(limit, inc),
                argument: argument.clone_incrementing(limit, inc),
            },
            PiType { binder, output } => PiType {
                binder: binder.clone_incrementing(limit, inc),
                output: output.clone_incrementing(limit + 1, inc),
            },
            Lambda { binder, body } => Lambda {
                binder: binder.clone_incrementing(limit, inc),
                body: body.clone_incrementing(limit + 1, inc),
            },
        };

        Self::from_inner(
            inner,
            self.abbreviation
                .as_ref()
                .map(|abbr| abbr.clone_incrementing(limit, inc)),
        )
    }

    /// Replaces the binder with de Bruijn index `id` with the given term, adding `inc` to the ids of all bound variables in the substituted term
    #[must_use]
    pub(super) fn replace_binder(self: &Rc<Self>, id: usize, expr: &TypedTerm) -> Rc<Self> {
        use TypedTermKindInner::*;

        let inner = match self.inner() {
            SortLiteral(_)
            | AdtName(_, _)
            | AdtConstructor(_, _, _)
            | AdtRecursor(_, _)
            | Axiom(_, _) => {
                return self.clone();
            }

            BoundVariable { index: eid, name } => {
                if *eid < id {
                    // If the binding in the expression is less than the binding being replaced, then it is unaffected.
                    BoundVariable {
                        index: *eid,
                        name: *name,
                    }
                } else if *eid == id {
                    // If the binding in the expression equals the binding being replaced, then return `expr`.
                    // Increment the indices of all bound variables in `expr` which point to variables outside `expr`.
                    expr.term.clone_incrementing(0, id).clone_inner()
                } else {
                    // If the binding in the expression is greater than the binding being replaced, then one binding has been
                    // removed between the binding and the reference, so the de Bruijn index needs to be reduced by one
                    BoundVariable {
                        index: eid - 1,
                        name: *name,
                    }
                }
            }
            Application { function, argument } => Application {
                function: function.replace_binder(id, expr),
                argument: argument.replace_binder(id, expr),
            },
            PiType { binder, output } => PiType {
                binder: binder.replace_binder(id, expr),
                output: output.replace_binder(id + 1, expr),
            },
            Lambda { binder, body } => Lambda {
                binder: binder.replace_binder(id, expr),
                body: body.replace_binder(id + 1, expr),
            },
        };

        Self::from_inner(
            inner,
            self.abbreviation
                .as_ref()
                .map(|abbr| abbr.replace_binder(id, expr)),
        )
    }

    pub fn with_abbreviation(&self, abbreviation: Abbreviation) -> Rc<Self> {
        Rc::new(Self {
            abbreviation: Some(Rc::new(abbreviation)),
            ..self.clone()
        })
    }

    pub fn with_abbreviation_from(&self, other: &Self) -> Rc<Self> {
        Rc::new(Self {
            abbreviation: other.abbreviation.clone(),
            ..self.clone()
        })
    }

    pub fn clear_abbreviation(&self) -> Rc<Self> {
        Rc::new(Self {
            abbreviation: None,
            ..self.clone()
        })
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

    fn clone_incrementing(self: &Rc<Self>, limit: usize, inc: usize) -> Rc<Self> {
        match self.as_ref() {
            Abbreviation::Constant(_, _) => self.clone(),
            Abbreviation::Application(abbr, term) => Rc::new(Self::Application(
                abbr.clone_incrementing(limit, inc),
                term.clone_incrementing(limit, inc),
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
    fn clone_incrementing(&self, limit: usize, inc: usize) -> Self {
        Self {
            span: self.span(),
            name: self.name,
            ty: self.ty.clone_incrementing(limit, inc),
        }
    }
}
