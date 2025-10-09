use crate::parser::PrettyPrint;
use crate::parser::atoms::ident::Identifier;
use crate::typeck::level::Level;
use crate::typeck::level::LevelArgs;
use crate::typeck::{AdtIndex, PrettyPrintContext, TypeError};
use std::io::Write;
use std::rc::Rc;

#[derive(Debug, Clone)]
#[cfg_attr(any(test, debug_assertions), derive(PartialEq))]
pub struct TypedTerm {
    level: Level,
    ty: TypedTermKind,
    term: TypedTermKind,
}

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
    pub(super) fn check_is_ty(&self) -> Result<Level, TypeError> {
        self.ty()
            .check_is_sort()
            .map_err(|_| TypeError::NotAType(self.clone()))
    }

    pub(super) fn value_of_type(value: TypedTermKind, ty: TypedTerm) -> TypedTerm {
        TypedTerm {
            level: ty.check_is_ty().expect("`ty` should have been a type"),
            ty: ty.term.clone(),
            term: value,
        }
    }

    pub(super) fn get_type(&self) -> TypedTerm {
        TypedTerm {
            level: self.level.succ(),
            ty: TypedTermKind::sort_literal(self.level.clone()),
            term: self.ty.clone(),
        }
    }

    fn shallow_eq(&self, other: &Self) -> bool {
        self.ty().ptr_eq(&other.ty()) && self.term().ptr_eq(&other.term())
    }

    pub(super) fn sort_literal(level: Level) -> TypedTerm {
        TypedTerm {
            level: level.succ().succ(),
            ty: TypedTermKind::sort_literal(level.succ()),
            term: TypedTermKind::sort_literal(level),
        }
    }

    /// Constructs a term referring to a bound variable. The given `ty` is used as-is, so the indices
    /// in it should be incremented from the type in the variable's binder.
    pub(super) fn bound_variable(
        index: usize,
        name: Option<Identifier>,
        ty: TypedTerm,
    ) -> TypedTerm {
        TypedTerm::value_of_type(TypedTermKind::bound_variable(index, name), ty)
    }

    pub(super) fn is_bound_variable(&self) -> Option<(usize, Option<Identifier>)> {
        match self.term().inner() {
            TypedTermKindInner::BoundVariable { index, name } => Some((*index, *name)),
            _ => None,
        }
    }

    pub(super) fn adt_name(adt_index: AdtIndex, ty: TypedTerm) -> TypedTerm {
        TypedTerm::value_of_type(TypedTermKind::adt_name(adt_index), ty)
    }

    pub(super) fn is_adt_name(&self) -> Option<AdtIndex> {
        match self.term().inner() {
            TypedTermKindInner::AdtName(adt) => Some(*adt),
            _ => None,
        }
    }

    pub(super) fn adt_constructor(
        adt_index: AdtIndex,
        constructor: usize,
        ty: TypedTerm,
    ) -> TypedTerm {
        TypedTerm::value_of_type(TypedTermKind::adt_constructor(adt_index, constructor), ty)
    }

    pub(super) fn adt_recursor(adt_index: AdtIndex, ty: TypedTerm) -> TypedTerm {
        TypedTerm::value_of_type(TypedTermKind::adt_recursor(adt_index), ty)
    }

    pub(super) fn make_pi_type(binder: TypedBinder, output: TypedTerm) -> TypedTerm {
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
            level: level.succ(),
            ty: TypedTermKind::sort_literal(level),
            term: TypedTermKind::pi_type(binder, output),
        }
    }

    pub(super) fn is_pi_type(&self) -> Option<(TypedBinder, TypedTerm)> {
        match self.term().inner() {
            TypedTermKindInner::PiType { binder, output } => Some((binder.clone(), output.clone())),
            _ => None,
        }
    }

    pub(super) fn make_application(
        function: TypedTerm,
        argument: TypedTerm,
        output: TypedTerm,
    ) -> TypedTerm {
        TypedTerm::value_of_type(TypedTermKind::application(function, argument), output)
    }

    pub(super) fn make_lambda(binder: TypedBinder, body: TypedTerm) -> TypedTerm {
        TypedTerm::value_of_type(
            TypedTermKind::lambda(binder.clone(), body.clone()),
            TypedTerm::make_pi_type(binder, body.get_type()),
        )
    }

    pub(super) fn is_lambda(&self) -> Option<(TypedBinder, TypedTerm)> {
        match self.term().inner() {
            TypedTermKindInner::Lambda { binder, body } => Some((binder.clone(), body.clone())),
            _ => None,
        }
    }

    pub(super) fn make_telescope(
        binders: impl IntoIterator<IntoIter: DoubleEndedIterator<Item = TypedBinder>>,
        output: TypedTerm,
    ) -> TypedTerm {
        binders
            .into_iter()
            .rfold(output, |acc, binder| TypedTerm::make_pi_type(binder, acc))
    }

    /// Decomposes a term as a telescope of pi types, returning the binders and the final output
    pub(super) fn decompose_telescope(mut self) -> (Vec<TypedBinder>, TypedTerm) {
        let mut indices = Vec::new();

        loop {
            self.term = self.term.reduce_root();

            match self.term.clone_inner() {
                TypedTermKindInner::PiType { binder, output } => {
                    indices.push(binder);
                    self = output;
                }

                t => {
                    return (
                        indices,
                        // Reconstruct `self`
                        TypedTerm {
                            term: TypedTermKind::from_inner(t),
                            ..self
                        },
                    );
                }
            }
        }
    }

    pub(super) fn make_application_stack(
        function: TypedTerm,
        params: impl IntoIterator<Item = TypedTermKind>,
    ) -> TypedTerm {
        let mut res = function;

        for param in params {
            let TypedTermKindInner::PiType { binder, output } = res.ty.clone_inner() else {
                panic!("`res` should have been a function type")
            };

            let param = TypedTerm::value_of_type(param, binder.ty);
            let output = output.replace_binder(0, &param);
            res = TypedTerm::make_application(res, param, output);
        }

        res
    }

    /// Decomposes a term as a stack of function applications, returning the underlying function and the arguments.
    pub(super) fn decompose_application_stack(mut self) -> (TypedTerm, Vec<TypedTerm>) {
        let mut args_reversed = Vec::new();

        loop {
            self.term = self.term.reduce_root();

            match self.term().clone_inner() {
                TypedTermKindInner::Application { function, argument } => {
                    args_reversed.push(argument);
                    self = function;
                }

                t => {
                    args_reversed.reverse();
                    return (
                        // Reconstruct `self`
                        TypedTerm {
                            term: TypedTermKind::from_inner(t),
                            ..self
                        },
                        args_reversed,
                    );
                }
            }
        }
    }

    /// Replaces the binder with de Bruijn index `id` with the given term, adding `id` to the ids of all bound variables in the new expression
    pub(super) fn replace_binder(&self, id: usize, expr: &TypedTerm) -> Self {
        Self {
            level: self.level.clone(),
            ty: self.ty.replace_binder(id, expr),
            term: self.term.replace_binder(id, expr),
        }
    }

    pub(super) fn instantiate(&self, level_args: &LevelArgs) -> Self {
        Self {
            level: self.level.instantiate_parameters(level_args),
            ty: self.ty.instantiate(level_args),
            term: self.term.instantiate(level_args),
        }
    }

    /// Clones the value, while incrementing all bound variable indices by `inc`
    pub(super) fn clone_incrementing(&self, limit: usize, inc: usize) -> Self {
        Self {
            level: self.level.clone(),
            ty: self.ty.clone_incrementing(limit, inc),
            term: self.term.clone_incrementing(limit, inc),
        }
    }

    #[must_use]
    pub(super) fn reduce_root(&self) -> Self {
        Self {
            term: self.term.reduce_root(),
            ..self.clone()
        }
    }

    /// Checks whether two terms are definitionally equal. This assumes that the two terms' types
    /// are themselves definitionally equal.
    pub(super) fn def_eq(&self, other: &Self) -> bool {
        debug_assert!(self.ty().def_eq(&other.ty()));

        if self == other {
            return true;
        }

        // Any two values of the same type in `Prop` are definitionally equal
        if self.level == Level::zero() {
            return true;
        }

        let self_ty = self.get_type().reduce_root();

        // If the terms being compared are functions, compare them by applying them both to a fresh
        // local variable and comparing the results
        if let Some((binder, output)) = self_ty.is_pi_type()
            && (self.is_lambda().is_some() || other.is_lambda().is_some())
        {
            let s = TypedTerm::make_application(
                self.clone_incrementing(0, 1),
                TypedTerm::bound_variable(0, None, binder.ty.clone()),
                output.clone(),
            )
            .reduce_root();

            let o = TypedTerm::make_application(
                other.clone_incrementing(0, 1),
                TypedTerm::bound_variable(0, None, binder.ty),
                output,
            )
            .reduce_root();

            return s.def_eq(&o);
        }

        // If none of the special cases apply, reduce the terms and compare them
        self.term().def_eq(&other.term())
    }
}

#[derive(Debug, Clone)]
#[cfg_attr(any(test, debug_assertions), derive(PartialEq))]
pub struct TypedTermKind(Rc<TypedTermKindInner>);

#[derive(Debug, Clone)]
#[cfg_attr(any(test, debug_assertions), derive(PartialEq))]
enum TypedTermKindInner {
    /// The keywords `Sort n`, `Prop` or `Type n`
    SortLiteral(Level),
    /// The name of an ADT
    AdtName(AdtIndex),
    /// The name of an ADT constructor
    AdtConstructor(AdtIndex, usize),
    /// The recursor of an ADT
    AdtRecursor(AdtIndex),
    /// A free variable in the context
    FreeVariable(Identifier),
    /// The bound variable of a lambda abstraction, using de Bruijn indices
    BoundVariable {
        /// The de Bruijn index
        index: usize,
        /// The name of the bound variable. This is for pretty printing only, and should not be used
        /// for type checking to avoid captures.
        name: Option<Identifier>,
    },
    /// A function application
    Application {
        function: TypedTerm,
        argument: TypedTerm,
    },
    /// A function / pi type
    PiType {
        binder: TypedBinder,
        output: TypedTerm,
    },
    /// A lambda abstraction
    Lambda {
        binder: TypedBinder,
        body: TypedTerm,
    },
}

impl TypedTermKindInner {
    fn shallow_eq(&self, other: &Self) -> bool {
        use TypedTermKindInner::*;

        match (self, other) {
            (SortLiteral(l1), SortLiteral(l2)) if l1 == l2 => true,
            (SortLiteral(_), _) => false,
            (AdtName(a1), AdtName(a2)) if a1 == a2 => true,
            (AdtName(_), _) => false,
            (AdtConstructor(a1, c1), AdtConstructor(a2, c2)) if a1 == a2 && c1 == c2 => true,
            (AdtConstructor(_, _), _) => false,
            (AdtRecursor(a1), AdtRecursor(a2)) if a1 == a2 => true,
            (AdtRecursor(_), _) => false,
            (FreeVariable(f1), FreeVariable(f2)) if f1 == f2 => true,
            (FreeVariable(_), _) => false,
            (
                BoundVariable {
                    index: i1,
                    name: n1,
                },
                BoundVariable {
                    index: i2,
                    name: n2,
                },
            ) if i1 == i2 && n1 == n2 => true,
            (BoundVariable { .. }, _) => false,
            (
                Application {
                    function: f1,
                    argument: a1,
                },
                Application {
                    function: f2,
                    argument: a2,
                },
            ) if f1.shallow_eq(f2) && a1.shallow_eq(a2) => true,
            (Application { .. }, _) => false,
            (
                PiType {
                    binder: b1,
                    output: o1,
                },
                PiType {
                    binder: b2,
                    output: o2,
                },
            ) if b1.shallow_eq(b2) && o1.shallow_eq(o2) => true,
            (PiType { .. }, _) => false,
            (
                Lambda {
                    binder: b1,
                    body: bo1,
                },
                Lambda {
                    binder: b2,
                    body: bo2,
                },
            ) if b1.shallow_eq(b2) && bo1.shallow_eq(bo2) => true,
            (Lambda { .. }, _) => false,
        }
    }
}

impl TypedTermKind {
    pub(super) fn sort_literal(level: Level) -> Self {
        Self(Rc::new(TypedTermKindInner::SortLiteral(level)))
    }

    pub(super) fn adt_name(adt: AdtIndex) -> Self {
        Self(Rc::new(TypedTermKindInner::AdtName(adt)))
    }

    pub(super) fn adt_constructor(adt: AdtIndex, constructor: usize) -> Self {
        Self(Rc::new(TypedTermKindInner::AdtConstructor(
            adt,
            constructor,
        )))
    }

    pub(super) fn adt_recursor(adt: AdtIndex) -> Self {
        Self(Rc::new(TypedTermKindInner::AdtRecursor(adt)))
    }

    pub(super) fn bound_variable(index: usize, name: Option<Identifier>) -> Self {
        Self(Rc::new(TypedTermKindInner::BoundVariable { index, name }))
    }

    pub(super) fn application(function: TypedTerm, argument: TypedTerm) -> Self {
        Self(Rc::new(TypedTermKindInner::Application {
            function,
            argument,
        }))
    }

    pub(super) fn pi_type(binder: TypedBinder, output: TypedTerm) -> Self {
        Self(Rc::new(TypedTermKindInner::PiType { binder, output }))
    }

    pub(super) fn lambda(binder: TypedBinder, body: TypedTerm) -> Self {
        Self(Rc::new(TypedTermKindInner::Lambda { binder, body }))
    }

    fn from_inner(inner: TypedTermKindInner) -> Self {
        Self(Rc::new(inner))
    }

    fn inner(&self) -> &TypedTermKindInner {
        self.0.as_ref()
    }

    fn clone_inner(&self) -> TypedTermKindInner {
        self.0.as_ref().clone()
    }

    fn ptr_eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }

    /// Checks that the term is a sort literal, returning its level
    pub(super) fn check_is_sort(&self) -> Result<Level, ()> {
        match self.inner() {
            TypedTermKindInner::SortLiteral(u) => Ok(u.clone()),
            _ => Err(()),
        }
    }

    /// Reduces the term until it is guaranteed that further reduction would not change the term's
    /// root kind
    #[must_use]
    pub(super) fn reduce_root(&self) -> Self {
        use TypedTermKindInner::*;

        let mut s = self.clone();

        loop {
            match s.clone_inner() {
                Application {
                    mut function,
                    argument,
                } => {
                    function.term = function.term.reduce_root();

                    match &function.term().inner() {
                        Lambda { binder: _, body } => {
                            s = body.term.replace_binder(0, &argument);
                        }
                        _ => break,
                    }
                }
                _ => break,
            }
        }

        s
    }

    pub(super) fn references_bound_variable(&self, id: usize) -> bool {
        use TypedTermKindInner::*;

        match self.inner() {
            SortLiteral(_)
            | AdtName(_)
            | AdtConstructor(_, _)
            | AdtRecursor(_)
            | FreeVariable(_) => false,

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

    #[must_use]
    pub(super) fn instantiate(&self, level_args: &LevelArgs) -> Self {
        use TypedTermKindInner::*;

        let inner = match self.inner() {
            SortLiteral(l) => SortLiteral(l.instantiate_parameters(level_args)),

            AdtName(_)
            | AdtConstructor(_, _)
            | AdtRecursor(_)
            | FreeVariable(_)
            | BoundVariable { .. } => return self.clone(),

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
    pub(super) fn clone_incrementing(&self, limit: usize, inc: usize) -> Self {
        use TypedTermKindInner::*;

        let inner = match self.inner() {
            SortLiteral(u) => SortLiteral(u.clone()),
            AdtName(adt) => AdtName(*adt),
            AdtConstructor(adt, cons) => AdtConstructor(*adt, *cons),
            AdtRecursor(adt) => AdtRecursor(*adt),
            FreeVariable(v) => FreeVariable(*v),
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
            SortLiteral(_)
            | AdtName(_)
            | AdtConstructor(_, _)
            | AdtRecursor(_)
            | FreeVariable(_) => return self.clone(),

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

    pub(super) fn def_eq(&self, other: &Self) -> bool {
        use TypedTermKindInner::*;

        if self == other {
            return true;
        }

        match (self.reduce_root().inner(), other.reduce_root().inner()) {
            (SortLiteral(su), SortLiteral(ou)) => su.def_eq(&ou),
            (SortLiteral(_), _) => false,
            (AdtName(sid), AdtName(oid)) => sid == oid,
            (AdtName(_), _) => false,
            (AdtConstructor(sadt, sid), AdtConstructor(oadt, oid)) => sadt == oadt && sid == oid,
            (AdtConstructor(_, _), _) => false,
            (AdtRecursor(sadt), AdtRecursor(oadt)) => sadt == oadt,
            (AdtRecursor(_), _) => false,
            (FreeVariable(sv), FreeVariable(ov)) => sv == ov,
            (FreeVariable(_), _) => false,
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
            ) => sf.def_eq(&of) && sa.def_eq(&oa),
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
            ) => sb.ty.def_eq(&ob.ty) && so.def_eq(&oo),
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
            ) => sbo.def_eq(&obo),
            (Lambda { .. }, _) => false,
        }
    }

    pub(super) fn forbid_references_to_adt(&self, adt: AdtIndex) -> Result<(), TypeError> {
        use TypedTermKindInner::*;

        match self.inner() {
            AdtName(id) | AdtConstructor(id, _) | AdtRecursor(id) if *id == adt => {
                Err(TypeError::InvalidLocationForAdtNameInConstructor(adt))
            }
            AdtName(_) | AdtConstructor(_, _) | AdtRecursor(_) => Ok(()),

            SortLiteral(_) | FreeVariable(_) | BoundVariable { .. } => Ok(()),

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

#[derive(Debug, Clone)]
#[cfg_attr(any(test, debug_assertions), derive(PartialEq))]
pub struct TypedBinder {
    pub name: Option<Identifier>,
    pub ty: TypedTerm,
}

impl TypedBinder {
    fn shallow_eq(&self, other: &Self) -> bool {
        self.name == other.name && self.ty.shallow_eq(&other.ty)
    }

    pub fn level(&self) -> Level {
        self.ty.check_is_ty().unwrap()
    }

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

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for TypedTerm {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext,
    ) -> std::io::Result<()> {
        // write!(out, "<")?;
        // self.term.pretty_print(out, context)?;
        // write!(out, " # ")?;
        // self.ty.pretty_print(out, context)?;
        // write!(out, ">")

        self.term.pretty_print(out, context)
    }
}

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for TypedTermKind {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext,
    ) -> std::io::Result<()> {
        use TypedTermKindInner::*;

        match self.inner() {
            SortLiteral(u) => {
                write!(out, "Sort ")?;
                u.pretty_print(out, context)
            }

            AdtName(adt) => context
                .environment
                .get_adt(*adt)
                .header
                .name
                .pretty_print(out, &context.interner()),
            AdtConstructor(adt, con) => context.environment.get_adt(*adt).constructors[*con]
                .name
                .pretty_print(out, &context.interner()),
            AdtRecursor(adt) => {
                context
                    .environment
                    .get_adt(*adt)
                    .header
                    .name
                    .pretty_print(out, &context.interner())?;
                write!(out, ".rec")
            }
            FreeVariable(name) => name.pretty_print(out, &context.interner()),
            BoundVariable { index, name } => {
                match name {
                    None => write!(out, "_")?,
                    Some(name) => name.pretty_print(out, &context.interner())?,
                }
                write!(out, "?{index}")
            }
            Application { function, argument } => {
                write!(out, "(")?;
                function.pretty_print(out, context)?;
                write!(out, " ")?;
                argument.pretty_print(out, context)?;
                write!(out, ")")
            }
            PiType { binder, output } => {
                write!(out, "(")?;
                binder.pretty_print(out, context)?;
                write!(out, " -> ")?;
                output.term.pretty_print(out, context)?;
                write!(out, ")")
            }
            Lambda { binder, body } => {
                write!(out, "(fun ")?;
                binder.pretty_print(out, context)?;
                write!(out, " => ")?;
                body.term.pretty_print(out, context)?;
                write!(out, ")")
            }
        }
    }
}

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for TypedBinder {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext<'a>,
    ) -> std::io::Result<()> {
        write!(out, "(")?;

        match self.name {
            None => write!(out, "_")?,
            Some(id) => id.pretty_print(out, &context.interner())?,
        };

        write!(out, ": ")?;
        self.ty.term.pretty_print(out, context)?;

        write!(out, ")")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::ast::parse_file;
    use crate::typeck::TypingEnvironment;

    #[test]
    fn test_make_application_stack() {
        let id_t = Identifier::dummy_val(0);
        let prop = TypedTerm::sort_literal(Level::zero());
        let ty = TypedTerm::sort_literal(Level::constant(1));

        let f = TypedTerm::adt_constructor(
            AdtIndex(0),
            0,
            TypedTerm::make_pi_type(
                TypedBinder {
                    name: Some(id_t),
                    ty: ty.clone(),
                },
                TypedTerm::make_pi_type(
                    TypedBinder {
                        name: None,
                        ty: TypedTerm::bound_variable(0, Some(id_t), ty.clone()),
                    },
                    prop.clone(),
                ),
            ),
        );

        let nat = TypedTerm::adt_name(AdtIndex(1), ty.clone());
        let zero = TypedTerm::adt_constructor(AdtIndex(1), 0, nat.clone());

        let nat_to_prop = TypedTerm::make_pi_type(
            TypedBinder {
                name: None,
                ty: nat.clone(),
            },
            prop.clone(),
        );

        let args = vec![nat.term.clone(), zero.term.clone()];

        assert_eq!(
            TypedTerm::make_application_stack(f.clone(), args),
            TypedTerm::make_application(
                TypedTerm::make_application(f, nat.clone(), nat_to_prop),
                zero.clone(),
                prop.clone()
            )
        );
    }

    #[test]
    fn test_replace_binder() {
        let sort_0 = TypedTerm::sort_literal(Level::constant(0));
        let adt_0 = TypedTerm::adt_name(AdtIndex(0), sort_0.clone());

        let id_x = Identifier::dummy_val(0);

        assert_eq!(
            TypedTerm::bound_variable(0, Some(id_x), sort_0.clone()).replace_binder(0, &adt_0),
            adt_0
        );

        assert_eq!(
            TypedTerm::make_pi_type(
                TypedBinder {
                    name: None,
                    ty: adt_0.clone()
                },
                TypedTerm::bound_variable(1, Some(id_x), sort_0.clone())
            )
            .replace_binder(0, &TypedTerm::bound_variable(1, Some(id_x), sort_0.clone())),
            TypedTerm::make_pi_type(
                TypedBinder {
                    name: None,
                    ty: adt_0.clone()
                },
                TypedTerm::bound_variable(2, Some(id_x), sort_0.clone())
            )
        );

        assert_eq!(
            TypedTerm::make_pi_type(
                TypedBinder {
                    name: None,
                    ty: adt_0.clone()
                },
                TypedTerm::bound_variable(2, Some(id_x), sort_0.clone())
            )
            .replace_binder(0, &TypedTerm::bound_variable(1, Some(id_x), sort_0.clone())),
            TypedTerm::make_pi_type(
                TypedBinder {
                    name: None,
                    ty: adt_0.clone()
                },
                TypedTerm::bound_variable(1, Some(id_x), sort_0)
            )
        );

        // TODO: test when the variable being replaced is in the binder of a Pi / lambda
    }

    fn assert_def_eq(env: &mut TypingEnvironment, t1: &str, t2: &str) {
        let t1 = env.resolve_term_from_string(t1);
        let t2 = env.resolve_term_from_string(t2);

        assert!(t1.def_eq(&t2));
    }

    fn assert_not_def_eq(env: &mut TypingEnvironment, t1: &str, t2: &str) {
        let t1 = env.resolve_term_from_string(t1);
        let t2 = env.resolve_term_from_string(t2);

        assert!(!t1.def_eq(&t2));
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

        let (interner, file) = parse_file(context).unwrap();
        let mut env = TypingEnvironment::new(interner);
        env.resolve_file(&file)
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
}
