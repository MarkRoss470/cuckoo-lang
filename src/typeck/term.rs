use crate::parser::PrettyPrint;
use crate::parser::atoms::ident::{Identifier, OwnedPath, Path};
use crate::typeck::level::{Level, LevelArgs};
use crate::typeck::{AdtIndex, PrettyPrintContext, TypeError, TypingContext};
use std::io::Write;
use std::rc::Rc;

#[derive(Debug, Clone)]
#[cfg_attr(any(test, debug_assertions), derive(PartialEq))]
pub struct TypedTerm {
    pub(super) level: Rc<Level>,
    pub(super) ty: TypedTermKind,
    pub(super) term: TypedTermKind,
    _priv: (),
}

impl TypedTerm {
    /// Checks that the term represents a type. If it is, returns what level it is in.
    pub(super) fn check_is_ty(&self) -> Result<Rc<Level>, TypeError> {
        self.ty
            .check_is_sort()
            .map_err(|_| TypeError::NotAType(self.clone()))
    }

    pub(super) fn get_type(&self) -> TypedTerm {
        TypedTerm {
            level: self.level.succ(),
            ty: TypedTermKind::SortLiteral(self.level.clone()),
            term: self.ty.clone(),
            _priv: (),
        }
    }

    pub(super) fn sort_literal(level: Rc<Level>) -> TypedTerm {
        TypedTerm {
            level: level.succ().succ(),
            ty: TypedTermKind::SortLiteral(level.succ()),
            term: TypedTermKind::SortLiteral(level),
            _priv: (),
        }
    }

    /// Constructs a term referring to a bound variable. The given `ty` is used as-is, so the indices
    /// in it should be incremented from the type in the variable's binder.
    pub(super) fn bound_variable(
        index: usize,
        name: Option<Identifier>,
        ty: TypedTerm,
    ) -> TypedTerm {
        TypedTerm {
            level: ty.check_is_ty().expect("`ty` should have been a type"),
            ty: ty.term,
            term: TypedTermKind::BoundVariable { index, name },
            _priv: (),
        }
    }

    pub(super) fn adt_name(adt_index: AdtIndex, ty: TypedTerm) -> TypedTerm {
        TypedTerm {
            level: ty.check_is_ty().expect("`ty` should have been a type"),
            ty: ty.term,
            term: TypedTermKind::AdtName(adt_index),
            _priv: (),
        }
    }

    pub(super) fn adt_constructor(
        adt_index: AdtIndex,
        constructor: usize,
        ty: TypedTerm,
    ) -> TypedTerm {
        TypedTerm {
            level: ty.check_is_ty().expect("`ty` should have been a type"),
            ty: ty.term,
            term: TypedTermKind::AdtConstructor(adt_index, constructor),
            _priv: (),
        }
    }

    pub(super) fn adt_recursor(adt_index: AdtIndex, ty: TypedTerm) -> TypedTerm {
        TypedTerm::value_of_type(TypedTermKind::AdtRecursor(adt_index), ty)
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
            ty: TypedTermKind::SortLiteral(level),
            term: TypedTermKind::PiType {
                binder: Box::new(binder),
                output: Box::new(output),
            },
            _priv: (),
        }
    }

    pub(super) fn make_application(
        function: TypedTerm,
        argument: TypedTerm,
        output: TypedTerm,
    ) -> TypedTerm {
        TypedTerm {
            level: output.ty.check_is_sort().unwrap(),
            ty: output.term,
            term: TypedTermKind::Application {
                function: Box::new(function),
                argument: Box::new(argument),
            },
            _priv: (),
        }
    }

    pub(super) fn value_of_type(value: TypedTermKind, ty: TypedTerm) -> TypedTerm {
        TypedTerm {
            level: ty.check_is_ty().unwrap(),
            ty: ty.term,
            term: value,
            _priv: (),
        }
    }

    pub(super) fn make_lambda(binder: TypedBinder, body: TypedTerm) -> TypedTerm {
        let level = binder.ty.check_is_ty().unwrap().smart_imax(&body.level);

        TypedTerm {
            level,
            ty: TypedTerm::make_pi_type(binder.clone(), body.get_type()).term,
            term: TypedTermKind::Lambda {
                binder: Box::new(binder),
                body: Box::new(body),
            },
            _priv: (),
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
            self.term.reduce_root();

            match self.term {
                TypedTermKind::PiType { binder, output } => {
                    indices.push(*binder);
                    self = *output;
                }

                t => {
                    return (
                        indices,
                        // Reconstruct `self`
                        TypedTerm { term: t, ..self },
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
            let TypedTermKind::PiType { binder, output } = res.ty.clone() else {
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
            self.term.reduce_root();

            match self.term {
                TypedTermKind::Application { function, argument } => {
                    args_reversed.push(*argument);
                    self = *function;
                }

                t => {
                    args_reversed.reverse();
                    return (
                        // Reconstruct `self`
                        TypedTerm { term: t, ..self },
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
            _priv: (),
        }
    }

    pub(super) fn instantiate(&self, level_args: &LevelArgs) -> Self {
        Self {
            level: self.level.instantiate_parameters(level_args),
            ty: self.ty.instantiate(level_args),
            term: self.term.instantiate(level_args),
            _priv: (),
        }
    }

    /// Clones the value, while incrementing all bound variable indices by `inc`
    pub(super) fn clone_incrementing(&self, limit: usize, inc: usize) -> Self {
        Self {
            level: self.level.clone(),
            ty: self.ty.clone_incrementing(limit, inc),
            term: self.term.clone_incrementing(limit, inc),
            _priv: (),
        }
    }

    /// Increments all bound variable indices which refer to variables of index `limit` or higher by amount `inc`
    pub(super) fn increment_binders_above(&mut self, limit: usize, inc: usize) {
        self.ty.increment_binders_above(limit, inc);
        self.term.increment_binders_above(limit, inc);
    }
}

// TODO: convert boxes to Rcs and clone less
#[cfg_attr(any(test, debug_assertions), derive(PartialEq))]
#[derive(Debug, Clone)]
pub enum TypedTermKind {
    /// The keywords `Sort n`, `Prop` or `Type n`
    SortLiteral(Rc<Level>),
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
        function: Box<TypedTerm>,
        argument: Box<TypedTerm>,
    },
    /// A function / pi type
    PiType {
        binder: Box<TypedBinder>,
        output: Box<TypedTerm>,
    },
    /// A lambda abstraction
    Lambda {
        binder: Box<TypedBinder>,
        body: Box<TypedTerm>,
    },
}

impl TypedTermKind {
    /// Checks that the term is a sort literal, returning its level
    pub(super) fn check_is_sort(&self) -> Result<Rc<Level>, ()> {
        match self {
            TypedTermKind::SortLiteral(u) => Ok(u.clone()),
            _ => Err(()),
        }
    }

    /// Reduces the term until it is guaranteed that further reduction would not change the term's
    /// root kind
    pub(super) fn reduce_root(&mut self) {
        use TypedTermKind::*;

        loop {
            match self {
                Application { function, argument } => {
                    function.term.reduce_root();

                    match &function.term {
                        Lambda { binder: _, body } => {
                            *self = body.term.replace_binder(0, argument);
                        }

                        _ => break,
                    }
                }
                _ => break,
            }
        }
    }

    pub(super) fn references_bound_variable(&self, id: usize) -> bool {
        match self {
            TypedTermKind::SortLiteral(_)
            | TypedTermKind::AdtName(_)
            | TypedTermKind::AdtConstructor(_, _)
            | TypedTermKind::AdtRecursor(_)
            | TypedTermKind::FreeVariable(_) => false,

            TypedTermKind::BoundVariable { index, name } => *index == id,
            TypedTermKind::Application { function, argument } => {
                function.term.references_bound_variable(id)
                    || argument.term.references_bound_variable(id)
            }
            TypedTermKind::PiType { binder, output } => {
                binder.ty.term.references_bound_variable(id)
                    || output.term.references_bound_variable(id + 1)
            }
            TypedTermKind::Lambda { binder, body } => {
                binder.ty.term.references_bound_variable(id)
                    || body.term.references_bound_variable(id + 1)
            }
        }
    }

    pub(super) fn instantiate(&self, level_args: &LevelArgs) -> Self {
        match self {
            Self::SortLiteral(l) => Self::SortLiteral(l.instantiate_parameters(level_args)),

            Self::AdtName(_)
            | Self::AdtConstructor(_, _)
            | Self::AdtRecursor(_)
            | Self::FreeVariable(_)
            | Self::BoundVariable { .. } => self.clone(),

            Self::Application { function, argument } => Self::Application {
                function: Box::new(function.instantiate(level_args)),
                argument: Box::new(argument.instantiate(level_args)),
            },
            Self::PiType { binder, output } => Self::PiType {
                binder: Box::new(binder.instantiate(level_args)),
                output: Box::new(output.instantiate(level_args)),
            },
            Self::Lambda { binder, body } => Self::Lambda {
                binder: Box::new(binder.instantiate(level_args)),
                body: Box::new(body.instantiate(level_args)),
            },
        }
    }

    /// Clones the value, while incrementing all bound variable indices above `limit` by `inc`
    pub(super) fn clone_incrementing(&self, limit: usize, inc: usize) -> Self {
        use TypedTermKind::*;

        match self {
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
                function: Box::new(function.clone_incrementing(limit, inc)),
                argument: Box::new(argument.clone_incrementing(limit, inc)),
            },
            PiType { binder, output } => PiType {
                binder: Box::new(binder.clone_incrementing(limit, inc)),
                output: Box::new(output.clone_incrementing(limit + 1, inc)),
            },
            Lambda { binder, body } => Lambda {
                binder: Box::new(binder.clone_incrementing(limit, inc)),
                body: Box::new(body.clone_incrementing(limit + 1, inc)),
            },
        }
    }

    /// Increments all bound variable indices which refer to variables of index `limit` or higher by amount `inc`
    pub(super) fn increment_binders_above(&mut self, limit: usize, inc: usize) {
        use TypedTermKind::*;

        match self {
            SortLiteral(_)
            | AdtName(_)
            | AdtConstructor(_, _)
            | AdtRecursor(_)
            | FreeVariable(_) => {}
            BoundVariable { index, name } => {
                if *index >= limit {
                    *index += inc;
                }
            }
            Application { function, argument } => {
                function.increment_binders_above(limit, inc);
                argument.increment_binders_above(limit, inc);
            }
            PiType { binder, output } => {
                binder.increment_binders_above(limit, inc);
                output.increment_binders_above(limit + 1, inc);
            }
            Lambda { binder, body } => {
                binder.increment_binders_above(limit, inc);
                body.increment_binders_above(limit + 1, inc);
            }
        }
    }

    /// Replaces the binder with de Bruijn index `id` with the given term, adding `inc` to the ids of all bound variables in the substituted term
    pub(super) fn replace_binder(&self, id: usize, expr: &TypedTerm) -> Self {
        use TypedTermKind::*;

        let res = match self {
            SortLiteral(_)
            | AdtName(_)
            | AdtConstructor(_, _)
            | AdtRecursor(_)
            | FreeVariable(_) => self.clone(),

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
                    expr.term.clone_incrementing(0, id)
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
                function: Box::new(function.replace_binder(id, expr)),
                argument: Box::new(argument.replace_binder(id, expr)),
            },
            PiType { binder, output } => PiType {
                binder: Box::new(binder.replace_binder(id, expr)),
                output: Box::new(output.replace_binder(id + 1, expr)),
            },
            Lambda { binder, body } => Lambda {
                binder: Box::new(binder.replace_binder(id, expr)),
                body: Box::new(body.replace_binder(id + 1, expr)),
            },
        };

        // dbg!(self);
        // dbg!(id);
        // dbg!(expr);
        // dbg!(&res);
        res
    }

    pub(super) fn def_eq(mut self, mut other: Self) -> bool {
        use TypedTermKind::*;

        self.reduce_root();
        other.reduce_root();

        match (self, other) {
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
            ) => sf.term.def_eq(of.term) && sa.term.def_eq(oa.term),
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
            ) => sb.ty.term.def_eq(ob.ty.term) && so.term.def_eq(oo.term),
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
            ) => sbo.term.def_eq(obo.term),
            (Lambda { .. }, _) => false,
        }
    }

    pub(super) fn forbid_references_to_adt(&self, adt: AdtIndex) -> Result<(), TypeError> {
        use TypedTermKind::*;

        match self {
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
    pub fn level(&self) -> Rc<Level> {
        self.ty.check_is_ty().unwrap()
    }

    /// Replaces the binder with de Bruijn index `id` with the given term
    pub(super) fn replace_binder(&self, id: usize, expr: &TypedTerm) -> Self {
        Self {
            name: self.name,
            ty: self.ty.replace_binder(id, expr),
        }
    }

    pub(super) fn instantiate(&self, level_args: &LevelArgs) -> Self {
        Self {
            name: self.name,
            ty: self.ty.instantiate(level_args),
        }
    }

    /// Clones the value, while incrementing all bound variable indices by `inc`
    fn clone_incrementing(&self, limit: usize, inc: usize) -> Self {
        Self {
            name: self.name,
            ty: self.ty.clone_incrementing(limit, inc),
        }
    }

    /// Increments all bound variable indices which refer to variables of index `limit` or higher by amount `inc`
    fn increment_binders_above(&mut self, limit: usize, inc: usize) {
        self.ty.increment_binders_above(limit, inc);
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
        use TypedTermKind::*;

        match self {
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
        // let (interner, ast) = parse_file(
        //     "
        //     data Eq (T : Type) : T -> T -> Prop where
        //
        //     data Nat : Type where
        //
        //     data SomeTy (m : Nat) (n : Nat) : Eq T m n -> Type where
        // ",
        // )
        // .unwrap();
        //
        // let mut env = TypingEnvironment::new(interner);
        // env.resolve_file(&ast).unwrap();
        //
        // let nat_path = env.adts[1].header.name.borrow();
        // let nat = env.resolve_path(nat_path, &LevelArgs::default()).unwrap();
        //
        // let some_ty_path = env.adts[2].header.name.borrow();
        // let some_ty = env
        //     .resolve_path(some_ty_path, &LevelArgs::default())
        //     .unwrap();
        //
        // assert_eq!(
        //     TypedTerm::make_application_stack(some_ty, vec![nat.term]),
        //     todo!()
        // );

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
    fn test_increment_binders_above() {
        let id_x = Identifier::dummy_val(0);
        
        assert_eq!(
            {
                let mut t = TypedTermKind::BoundVariable {
                    index: 0,
                    name: Some(id_x),
                };
                t.increment_binders_above(0, 5);
                t
            },
            TypedTermKind::BoundVariable {
                index: 5,
                name: Some(id_x)
            }
        );

        assert_eq!(
            {
                let mut t = TypedTermKind::BoundVariable {
                    index: 0,
                    name: Some(id_x),
                };
                t.increment_binders_above(1, 5);
                t
            },
            TypedTermKind::BoundVariable {
                index: 0,
                name: Some(id_x)
            }
        );

        let ty = Level::constant(1);

        let binder = TypedBinder {
            name: None,
            ty: TypedTerm::sort_literal(ty.clone()),
        };

        {
            let t = TypedTerm::make_pi_type(
                binder.clone(),
                TypedTerm::bound_variable(
                    0,
                    Some(id_x),
                    TypedTerm::sort_literal(ty.clone()),
                ),
            );
            assert_eq!(
                {
                    let mut t = t.clone();
                    t.increment_binders_above(0, 5);
                    t
                },
                t
            );
        }

        {
            let t = TypedTerm::make_pi_type(
                binder,
                TypedTerm::bound_variable(
                    1,
                    Some(id_x),
                    TypedTerm::sort_literal(ty.clone()),
                ),
            );

            assert_eq!(
                {
                    let mut t = t.term.clone();
                    t.increment_binders_above(0, 5);
                    t
                },
                TypedTerm::make_pi_type(
                    TypedBinder {
                        name: None,
                        ty: TypedTerm::sort_literal(ty.clone()),
                    },
                    TypedTerm::bound_variable(
                        6,
                        Some(id_x),
                        TypedTerm::sort_literal(ty.clone())
                    )
                )
                .term
            );
        }
    }

    #[test]
    fn test_replace_binder() {
        let sort_0 = TypedTerm::sort_literal(Level::constant(0));
        let adt_0 = TypedTerm::adt_name(AdtIndex(0), sort_0.clone());

        let id_x = Identifier::dummy_val(0);
        
        assert_eq!(
            TypedTerm::bound_variable(0, Some(id_x), sort_0.clone())
                .replace_binder(0, &adt_0),
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
            .replace_binder(
                0,
                &TypedTerm::bound_variable(1, Some(id_x), sort_0.clone())
            ),
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
            .replace_binder(
                0,
                &TypedTerm::bound_variable(1, Some(id_x), sort_0.clone())
            ),
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
}
