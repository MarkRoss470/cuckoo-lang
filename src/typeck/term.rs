use crate::parser::PrettyPrint;
use crate::parser::ast::term::{Binder, Term, LevelExpr, binder};
use crate::parser::atoms::ident::{Identifier, OwnedPath, Path};
use crate::typeck::level::{Level, LevelArgs};
use crate::typeck::{AdtIndex, PrettyPrintContext, TypeError, TypingContext};
use std::io::Write;
use std::rc::Rc;

#[derive(Debug, Clone)]
#[cfg_attr(test, derive(PartialEq, Eq))]
pub struct TypedTerm {
    pub(super) level: Rc<Level>,
    pub(super) ty: TypedTermKind,
    pub(super) term: TypedTermKind,
}

impl TypedTerm {
    /// Checks that the term represents a type. If it is, returns what level it is in.
    pub(super) fn check_is_ty(&self) -> Result<Rc<Level>, TypeError> {
        match &self.ty {
            TypedTermKind::SortLiteral(u) => Ok(u.clone()),
            _ => Err(TypeError::NotAType(self.clone())),
        }
    }

    /// Decomposes a term as a telescope of pi types, returning the binders and the final output
    pub(super) fn into_telescope(mut self) -> (Vec<TypedBinder>, TypedTerm) {
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

    /// Decomposes a term as a stack of function applications, returning the underlying function and the arguments.
    pub(super) fn into_application_stack(mut self) -> (TypedTerm, Vec<TypedTerm>) {
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
    fn clone_incrementing(&self, limit: usize, inc: usize) -> Self {
        Self {
            level: self.level.clone(),
            ty: self.ty.clone_incrementing(limit, inc),
            term: self.term.clone_incrementing(limit, inc),
        }
    }

    /// Increments all bound variable indices which refer to variables of index `limit` or higher by amount `inc`
    fn increment_binders_above(&mut self, limit: usize, inc: usize) {
        self.ty.increment_binders_above(limit, inc);
        self.term.increment_binders_above(limit, inc);
    }
}

// TODO: convert boxes to Rcs and clone less
#[cfg_attr(test, derive(PartialEq, Eq))]
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
        name: Identifier,
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
#[cfg_attr(test, derive(PartialEq, Eq))]
pub struct TypedBinder {
    pub name: Option<Identifier>,
    pub ty: TypedTerm,
}

impl TypedBinder {
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

impl<'a> TypingContext<'a> {
    pub(super) fn resolve_term(&self, term: &Term) -> Result<TypedTerm, TypeError> {
        match term {
            Term::Sort(u) => {
                let u = self.resolve_level(u)?;
                let us = Rc::new(Level::Succ(u.clone()));
                let uss = Rc::new(Level::Succ(us.clone()));

                Ok(TypedTerm {
                    level: uss,
                    ty: TypedTermKind::SortLiteral(us),
                    term: TypedTermKind::SortLiteral(u.clone()),
                })
            }
            Term::Path(id, level_args) => {
                self.resolve_path(id.borrow(), &self.resolve_level_args(level_args)?)
            }
            Term::Application { function, argument } => {
                self.resolve_application(function, argument)
            }
            Term::PiType { binder, output } => self.resolve_pi_type(binder, output),
            Term::Lambda { binder, body } => self.resolve_lambda(binder, body),
        }
    }

    /// Resolves an identifier in the context. On success, returns the associated term as well as the number of
    /// binders between that binder's introduction and the current context - the binders in the term need to be
    /// increased by this number, which is done in [`resolve_identifier`][Self::resolve_identifier]
    fn resolve_path_inner(
        &self,
        path: Path,
        level_args: &LevelArgs,
    ) -> Result<(TypedTerm, usize), TypeError> {
        match self {
            TypingContext::Root(env) => env.resolve_path(path, level_args).map(|t| (t, 0)),
            TypingContext::Binder { binder, parent } => {
                let (first, rest) = path.split_first();

                // Check whether the identifier matches the binder
                if let Some(name) = binder.name {
                    if first == name {
                        // If the identifier resolved to the local variable but there are more segments in the path, give an error
                        if rest.is_some() {
                            return Err(TypeError::LocalVariableIsNotANamespace(OwnedPath::from_id(first)));
                        }

                        let level = binder
                            .ty
                            .ty
                            .check_is_sort()
                            .expect("Binder type should have been a type");

                        return Ok((
                            TypedTerm {
                                level,
                                ty: binder.ty.term.clone(),
                                term: TypedTermKind::BoundVariable {
                                    index: 0,
                                    name: first,
                                },
                            },
                            0,
                        ));
                    }
                }

                parent
                    .resolve_path_inner(path, level_args)
                    .map(|(t, i)| (t, i + 1))
            }
        }
    }

    /// Resolves a path in the current context
    fn resolve_path(&self, path: Path, level_args: &LevelArgs) -> Result<TypedTerm, TypeError> {
        self.resolve_path_inner(path, level_args)
            .map(|(mut t, i)| {
                // The term includes its own binder while the type doesn't, so the type needs to be incremented by one more than the term
                t.ty.increment_binders_above(0, i + 1);
                t.term.increment_binders_above(0, i);
                t
            })
    }

    fn resolve_application(
        &self,
        function: &Term,
        argument: &Term,
    ) -> Result<TypedTerm, TypeError> {
        // Type check the function and argument
        let mut function = self.resolve_term(function)?;
        let mut argument = self.resolve_term(argument)?;

        // Reduce the type of the function
        function.ty.reduce_root();

        // println!("Function and argument:");
        // self.environment().pretty_println_val(&function.term);
        // self.environment().pretty_println_val(&function.ty);
        // self.environment().pretty_println_val(&argument.term);
        // self.environment().pretty_println_val(&argument.ty);
        // println!();

        // Check that the function has a function type
        let TypedTermKind::PiType { binder, output } = &mut function.ty else {
            return Err(TypeError::NotAFunction(function));
        };

        // Check that the type of the argument matches the input type of the function
        // TODO: do this check without cloning
        if !binder.ty.term.clone().def_eq(argument.ty.clone()) {
            return Err(TypeError::MismatchedTypes {
                term: argument,
                expected: binder.ty.clone(),
            });
        }

        // Replace instances of the binder in the output type with the argument
        let output_ty = output.term.replace_binder(0, &argument);

        Ok(TypedTerm {
            level: output.level.clone(),
            ty: output_ty,
            term: TypedTermKind::Application {
                function: Box::new(function),
                argument: Box::new(argument),
            },
        })
    }

    fn resolve_pi_type(&self, binder: &Binder, output: &Term) -> Result<TypedTerm, TypeError> {
        // Resolve the type of the binder, and check that it actually is a type
        let binder_ty = self.resolve_term(&binder.ty)?;
        let binder_level = binder_ty.check_is_ty()?;
        let binder = TypedBinder {
            name: binder.name,
            ty: binder_ty,
        };

        // Construct a new typing context which includes the new binder
        let c = TypingContext::Binder {
            binder: &binder,
            parent: self,
        };

        // Resolve the output type in this new context
        let output = c.resolve_term(&output)?;
        let output_level = output.check_is_ty()?;

        // Calculate the level of the new type
        let level = binder_level.smart_imax(&output_level);

        Ok(TypedTerm {
            level: level.succ(),
            ty: TypedTermKind::SortLiteral(level),
            term: TypedTermKind::PiType {
                binder: Box::new(binder),
                output: Box::new(output),
            },
        })
    }

    fn resolve_lambda(&self, binder: &Binder, body: &Term) -> Result<TypedTerm, TypeError> {
        // Resolve the type of the binder, and check that it actually is a type
        let binder_ty = self.resolve_term(&binder.ty)?;
        let binder_level = binder_ty.check_is_ty()?;
        let binder = TypedBinder {
            name: binder.name,
            ty: binder_ty,
        };

        // Construct a new typing context which includes the new binder
        let c = TypingContext::Binder {
            binder: &binder,
            parent: self,
        };

        // Resolve the output type in this new context
        let body = c.resolve_term(&body)?;

        // Calculate the level of the new term
        let level = binder_level.smart_imax(&body.level);

        Ok(TypedTerm {
            level,
            ty: TypedTermKind::PiType {
                binder: Box::new(binder.clone()),
                output: Box::new(TypedTerm {
                    level: body.level.succ(),
                    ty: TypedTermKind::SortLiteral(body.level.clone()),
                    term: body.ty.clone(),
                }),
            },
            term: TypedTermKind::Lambda {
                binder: Box::new(binder),
                body: Box::new(body),
            },
        })
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
                .name
                .pretty_print(out, context.interner()),
            AdtConstructor(adt, con) => context.environment.get_adt(*adt).constructors[*con]
                .name
                .pretty_print(out, context.interner()),
            AdtRecursor(adt) => {
                context
                    .environment
                    .get_adt(*adt)
                    .name
                    .pretty_print(out, context.interner())?;
                write!(out, ".rec")
            }
            FreeVariable(name) => name.pretty_print(out, context.interner()),
            BoundVariable { index, name } => {
                name.pretty_print(out, context.interner())?;
                write!(out, "?{index}")
            }
            Application { function, argument } => {
                write!(out, "(")?;
                function.term.pretty_print(out, context)?;
                write!(out, " ")?;
                argument.term.pretty_print(out, context)?;
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
            Some(id) => id.pretty_print(out, context.interner())?,
        };

        write!(out, ": ")?;
        self.ty.term.pretty_print(out, context)?;

        write!(out, ")")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Interner;
    use crate::parser::ast::Ast;
    use crate::typeck::TypingEnvironment;

    #[test]
    fn test_increment_binders_above() {
        assert_eq!(
            {
                let mut t = TypedTermKind::BoundVariable {
                    index: 0,
                    name: Identifier::dummy(),
                };
                t.increment_binders_above(0, 5);
                t
            },
            TypedTermKind::BoundVariable {
                index: 5,
                name: Identifier::dummy()
            }
        );

        assert_eq!(
            {
                let mut t = TypedTermKind::BoundVariable {
                    index: 0,
                    name: Identifier::dummy(),
                };
                t.increment_binders_above(1, 5);
                t
            },
            TypedTermKind::BoundVariable {
                index: 0,
                name: Identifier::dummy()
            }
        );

        let ty = Level::constant(1);
        let tys = ty.succ();
        let tyss = tys.succ();

        {
            let t = TypedTermKind::PiType {
                binder: Box::new(TypedBinder {
                    name: None,
                    ty: TypedTerm {
                        level: tyss.clone(),
                        ty: TypedTermKind::SortLiteral(tys.clone()),
                        term: TypedTermKind::SortLiteral(ty.clone()),
                    },
                }),
                output: Box::new(TypedTerm {
                    level: tys.clone(),
                    ty: TypedTermKind::SortLiteral(ty.clone()),
                    term: TypedTermKind::BoundVariable {
                        index: 0,
                        name: Identifier::dummy(),
                    },
                }),
            };
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
            let t = TypedTermKind::PiType {
                binder: Box::new(TypedBinder {
                    name: None,
                    ty: TypedTerm {
                        level: tyss.clone(),
                        ty: TypedTermKind::SortLiteral(tys.clone()),
                        term: TypedTermKind::SortLiteral(ty.clone()),
                    },
                }),
                output: Box::new(TypedTerm {
                    level: tys.clone(),
                    ty: TypedTermKind::SortLiteral(ty.clone()),
                    term: TypedTermKind::BoundVariable {
                        index: 1,
                        name: Identifier::dummy(),
                    },
                }),
            };
            assert_eq!(
                {
                    let mut t = t.clone();
                    t.increment_binders_above(0, 5);
                    t
                },
                TypedTermKind::PiType {
                    binder: Box::new(TypedBinder {
                        name: None,
                        ty: TypedTerm {
                            level: tyss.clone(),
                            ty: TypedTermKind::SortLiteral(tys.clone()),
                            term: TypedTermKind::SortLiteral(ty.clone()),
                        },
                    }),
                    output: Box::new(TypedTerm {
                        level: tys.clone(),
                        ty: TypedTermKind::SortLiteral(ty.clone()),
                        term: TypedTermKind::BoundVariable {
                            index: 6,
                            name: Identifier::dummy(),
                        },
                    }),
                }
            );
        }
    }

    #[test]
    fn test_replace_binder() {
        let ty = Level::constant(1);
        let tys = ty.succ();
        let tyss = tys.succ();

        assert_eq!(
            TypedTermKind::BoundVariable {
                index: 0,
                name: Identifier::dummy()
            }
            .replace_binder(
                0,
                &TypedTerm {
                    level: tys.clone(),
                    ty: TypedTermKind::SortLiteral(ty.clone()),
                    term: TypedTermKind::AdtName(AdtIndex(0))
                }
            ),
            TypedTermKind::AdtName(AdtIndex(0))
        );

        assert_eq!(
            TypedTermKind::PiType {
                binder: Box::new(TypedBinder {
                    name: None,
                    ty: TypedTerm {
                        level: tys.clone(),
                        ty: TypedTermKind::SortLiteral(ty.clone()),
                        term: TypedTermKind::AdtName(AdtIndex(0)),
                    }
                }),
                output: Box::new(TypedTerm {
                    level: tys.clone(),
                    ty: TypedTermKind::SortLiteral(ty.clone()),
                    term: TypedTermKind::BoundVariable {
                        index: 1,
                        name: Identifier::dummy()
                    }
                }),
            }
            .replace_binder(
                0,
                &TypedTerm {
                    level: tys.clone(),
                    ty: TypedTermKind::SortLiteral(ty.clone()),
                    term: TypedTermKind::BoundVariable {
                        index: 1,
                        name: Identifier::dummy()
                    }
                }
            ),
            TypedTermKind::PiType {
                binder: Box::new(TypedBinder {
                    name: None,
                    ty: TypedTerm {
                        level: tys.clone(),
                        ty: TypedTermKind::SortLiteral(ty.clone()),
                        term: TypedTermKind::AdtName(AdtIndex(0)),
                    }
                }),
                output: Box::new(TypedTerm {
                    level: tys.clone(),
                    ty: TypedTermKind::SortLiteral(ty.clone()),
                    term: TypedTermKind::BoundVariable {
                        index: 2,
                        name: Identifier::dummy()
                    }
                })
            }
        );

        assert_eq!(
            TypedTermKind::PiType {
                binder: Box::new(TypedBinder {
                    name: None,
                    ty: TypedTerm {
                        level: tys.clone(),
                        ty: TypedTermKind::SortLiteral(ty.clone()),
                        term: TypedTermKind::AdtName(AdtIndex(0)),
                    }
                }),
                output: Box::new(TypedTerm {
                    level: tys.clone(),
                    ty: TypedTermKind::SortLiteral(ty.clone()),
                    term: TypedTermKind::BoundVariable {
                        index: 2,
                        name: Identifier::dummy()
                    }
                }),
            }
            .replace_binder(
                0,
                &TypedTerm {
                    level: tys.clone(),
                    ty: TypedTermKind::SortLiteral(ty.clone()),
                    term: TypedTermKind::BoundVariable {
                        index: 1,
                        name: Identifier::dummy()
                    }
                }
            ),
            TypedTermKind::PiType {
                binder: Box::new(TypedBinder {
                    name: None,
                    ty: TypedTerm {
                        level: tys.clone(),
                        ty: TypedTermKind::SortLiteral(ty.clone()),
                        term: TypedTermKind::AdtName(AdtIndex(0)),
                    }
                }),
                output: Box::new(TypedTerm {
                    level: tys.clone(),
                    ty: TypedTermKind::SortLiteral(ty.clone()),
                    term: TypedTermKind::BoundVariable {
                        index: 1,
                        name: Identifier::dummy()
                    }
                })
            }
        );
    }

    #[test]
    fn test_resolve_identifier() {
        let ast = Ast {
            interner: Interner::new(),
            items: vec![],
        };
        let env = TypingEnvironment::new(&ast);

        let id_t = Identifier::dummy_val(0);
        let id_x = Identifier::dummy_val(1);

        let context = TypingContext::Root(&env);

        let ty = Level::constant(1);
        let tys = ty.succ();
        let tyss = tys.succ();

        let context = TypingContext::Binder {
            binder: &TypedBinder {
                name: Some(id_t),
                ty: TypedTerm {
                    level: tyss.clone(),
                    ty: TypedTermKind::SortLiteral(tys.clone()),
                    term: TypedTermKind::SortLiteral(ty.clone()),
                },
            },
            parent: &context,
        };

        let context = TypingContext::Binder {
            binder: &TypedBinder {
                name: Some(id_x),
                ty: TypedTerm {
                    level: tys.clone(),
                    ty: TypedTermKind::SortLiteral(ty.clone()),
                    term: TypedTermKind::BoundVariable {
                        index: 0,
                        name: id_t,
                    },
                },
            },
            parent: &context,
        };

        assert_eq!(
            context
                .resolve_path(Path::from_id(&id_t), &LevelArgs::default())
                .unwrap(),
            TypedTerm {
                level: tys.clone(),
                ty: TypedTermKind::SortLiteral(ty.clone()),
                term: TypedTermKind::BoundVariable {
                    index: 1,
                    name: id_t
                },
            },
        );

        assert_eq!(
            context
                .resolve_path(Path::from_id(&id_x), &LevelArgs::default())
                .unwrap(),
            TypedTerm {
                level: ty.clone(),
                ty: TypedTermKind::BoundVariable {
                    index: 1,
                    name: id_t
                },
                term: TypedTermKind::BoundVariable {
                    index: 0,
                    name: id_x
                },
            },
        );
    }
}
