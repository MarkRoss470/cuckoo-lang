use crate::typeck::level::LevelArgs;
use crate::typeck::term::{TypedBinder, TypedTerm, TypedTermKind, TypedTermKindInner};

impl TypedTerm {
    /// Replaces the binder with de Bruijn index `id` with the given term, adding `id` to the ids of all bound variables in the new expression
    pub fn replace_binder(&self, id: usize, expr: &TypedTerm) -> Self {
        Self {
            level: self.level.clone(),
            ty: self.ty.replace_binder(id, expr),
            term: self.term.replace_binder(id, expr),
        }
    }

    pub fn instantiate(&self, level_args: &LevelArgs) -> Self {
        Self {
            level: self.level.instantiate_parameters(level_args),
            ty: self.ty.instantiate(level_args),
            term: self.term.instantiate(level_args),
        }
    }

    /// Clones the value, while incrementing all bound variable indices by `inc`
    pub fn clone_incrementing(&self, limit: usize, inc: usize) -> Self {
        Self {
            level: self.level.clone(),
            ty: self.ty.clone_incrementing(limit, inc),
            term: self.term.clone_incrementing(limit, inc),
        }
    }
}

impl TypedTermKind {
    #[must_use]
    pub(super) fn instantiate(&self, level_args: &LevelArgs) -> Self {
        use TypedTermKindInner::*;

        let inner = match self.inner() {
            SortLiteral(l) => SortLiteral(l.instantiate_parameters(level_args)),

            AdtName(_) | AdtConstructor(_, _) | AdtRecursor(_) | BoundVariable { .. } => {
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

        // If the instantiation hasn't fundamentally changed anything, return `self` rather
        // than allocating a new `Rc`
        if self.inner().shallow_eq(&inner) {
            self.clone()
        } else {
            Self::from_inner(inner)
        }
    }

    // TODO: rename as cloning is no longer special
    /// Clones the value, while incrementing all bound variable indices above `limit` by `inc`
    #[must_use]
    pub fn clone_incrementing(&self, limit: usize, inc: usize) -> Self {
        use TypedTermKindInner::*;

        let inner = match self.inner() {
            SortLiteral(u) => SortLiteral(u.clone()),
            AdtName(adt) => AdtName(*adt),
            AdtConstructor(adt, cons) => AdtConstructor(*adt, *cons),
            AdtRecursor(adt) => AdtRecursor(*adt),
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

        // If the incrementing hasn't fundamentally changed anything, return `self` rather
        // than allocating a new `Rc`
        if self.inner().shallow_eq(&inner) {
            self.clone()
        } else {
            Self::from_inner(inner)
        }
    }

    /// Replaces the binder with de Bruijn index `id` with the given term, adding `inc` to the ids of all bound variables in the substituted term
    #[must_use]
    pub(super) fn replace_binder(&self, id: usize, expr: &TypedTerm) -> Self {
        use TypedTermKindInner::*;

        let inner = match self.inner() {
            SortLiteral(_) | AdtName(_) | AdtConstructor(_, _) | AdtRecursor(_) => {
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

        // If the replacement hasn't fundamentally changed anything, return `self` rather
        // than allocating a new `Rc`
        if self.inner().shallow_eq(&inner) {
            self.clone()
        } else {
            Self::from_inner(inner)
        }
    }
}

impl TypedBinder {
    /// Replaces the binder with de Bruijn index `id` with the given term
    #[must_use]
    pub(super) fn replace_binder(&self, id: usize, expr: &TypedTerm) -> Self {
        Self {
            name: self.name,
            ty: self.ty.replace_binder(id, expr),
        }
    }

    #[must_use]
    pub(super) fn instantiate(&self, level_args: &LevelArgs) -> Self {
        Self {
            name: self.name,
            ty: self.ty.instantiate(level_args),
        }
    }

    /// Clones the value, while incrementing all bound variable indices by `inc`
    #[must_use]
    fn clone_incrementing(&self, limit: usize, inc: usize) -> Self {
        Self {
            name: self.name,
            ty: self.ty.clone_incrementing(limit, inc),
        }
    }
}
