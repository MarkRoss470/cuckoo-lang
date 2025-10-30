use crate::typeck::TypedTerm;
use crate::typeck::term::{TypedBinder, TypedTermKind, TypedTermKindInner};

impl TypedTerm {
    /// Checks two terms for structural equality.
    /// If `check_names` is true, the names of binders will be compared, otherwise they will be ignored.
    pub fn equiv(&self, other: &Self, check_names: bool) -> bool {
        self.level.def_eq(&other.level)
            && self.ty.equiv(&other.ty, check_names)
            && self.term.equiv(&other.term, check_names)
    }
}

impl TypedTermKind {
    pub fn equiv(&self, other: &Self, check_names: bool) -> bool {
        self.inner().equiv(other.inner(), check_names)
    }
}

impl TypedTermKindInner {
    #[rustfmt::skip]
    pub fn equiv(&self, other: &Self, check_names: bool) -> bool {
        use TypedTermKindInner::*;

        match (self, other) {
            (SortLiteral(l1), SortLiteral(l2)) => l1 == l2,
            (SortLiteral(_), _) => false,
            (
                AdtName(adt1, args1),
                AdtName(adt2, args2),
            ) => adt1 == adt2 && args1 == args2,
            (AdtName(_, _), _) => false,
            (
                AdtConstructor(adt1, c1, args1),
                AdtConstructor(adt2, c2, args2),
            ) => adt1 == adt2 && c1 == c2 && args1 == args2,
            (AdtConstructor(_, _, _), _) => false,
            (
                AdtRecursor(adt1, args1),
                AdtRecursor(adt2, args2),
            ) => adt1 == adt2 && args1 == args2,
            (AdtRecursor(_, _), _) => false,
            (
                Axiom(ax1, args1),
                Axiom(ax2, args2),
            ) => ax1 == ax2 && args1 == args2,
            (Axiom(_, _), _) => false,
            (
                BoundVariable { index: i1, name: n1,},
                BoundVariable { index: i2, name: n2,},
            ) => i1 == i2 && (!check_names || n1 == n2),
            (BoundVariable { .. }, _) => false,
            (
                Application { function: f1, argument: a1, },
                Application { function: f2, argument: a2, },
            ) => f1.equiv(f2, check_names) && a1.equiv(a2, check_names),
            (Application { .. }, _) => false,
            (
                PiType { binder: b1, output: o1, },
                PiType { binder: b2, output: o2, },
            ) => b1.equiv(b2, check_names) && o1.equiv(o2, check_names),
            (PiType { .. }, _) => false,
            (
                Lambda { binder: bi1, body: bo1, },
                Lambda { binder: bi2, body: bo2, },
            ) => bi1.equiv(bi2, check_names) && bo1.equiv(bo2, check_names),
            (Lambda { .. }, _) => false,
        }
    }
}

impl TypedBinder {
    pub fn equiv(&self, other: &Self, check_names: bool) -> bool {
        (!check_names || self.name == other.name) && self.ty.equiv(&other.ty, check_names)
    }
}
