use crate::parser::PrettyPrint;
use crate::parser::ast::term::Universe;
use crate::parser::atoms::Identifier;
use crate::typeck::{AdtIndex, PrettyPrintContext, TypeError};
use std::io::Write;

#[derive(Debug, Clone)]
#[cfg_attr(test, derive(PartialEq, Eq))]
pub struct TypedTerm {
    pub(super) universe: Universe,
    pub(super) ty: TypedTermKind,
    pub(super) term: TypedTermKind,
}

impl TypedTerm {
    /// Checks that the term represents a type. If it is, returns what universe it is in.
    pub(super) fn check_is_ty(&self) -> Result<Universe, TypeError> {
        match self.ty {
            TypedTermKind::SortLiteral(u) => Ok(u),
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
            universe: self.universe,
            ty: self.ty.replace_binder(id, expr),
            term: self.term.replace_binder(id, expr),
        }
    }

    /// Clones the value, while incrementing all bound variable indices by `inc`
    fn clone_incrementing(&self, limit: usize, inc: usize) -> Self {
        Self {
            universe: self.universe,
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

#[derive(Debug, Clone)]
#[cfg_attr(test, derive(PartialEq, Eq))]
pub enum TypedTermKind {
    /// The keywords `Prop` or `Type n`
    SortLiteral(Universe),
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
    /// Checks that the term is a sort literal, returning its universe
    pub(super) fn check_is_sort(&self) -> Result<Universe, ()> {
        match self {
            TypedTermKind::SortLiteral(u) => Ok(*u),
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

    /// Clones the value, while incrementing all bound variable indices above `limit` by `inc`
    pub(super) fn clone_incrementing(&self, limit: usize, inc: usize) -> Self {
        use TypedTermKind::*;

        match self {
            SortLiteral(u) => SortLiteral(*u),
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
            (SortLiteral(su), SortLiteral(ou)) => su == ou,
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

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for TypedTermKind {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext,
    ) -> std::io::Result<()> {
        use TypedTermKind::*;

        match self {
            SortLiteral(u) => u.pretty_print(out, ()),

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

        {
            let t = TypedTermKind::PiType {
                binder: Box::new(TypedBinder {
                    name: None,
                    ty: TypedTerm {
                        universe: Universe::TYPE.succ().succ(),
                        ty: TypedTermKind::SortLiteral(Universe::TYPE.succ()),
                        term: TypedTermKind::SortLiteral(Universe::TYPE),
                    },
                }),
                output: Box::new(TypedTerm {
                    universe: Universe::TYPE.succ(),
                    ty: TypedTermKind::SortLiteral(Universe::TYPE),
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
                        universe: Universe::TYPE.succ().succ(),
                        ty: TypedTermKind::SortLiteral(Universe::TYPE.succ()),
                        term: TypedTermKind::SortLiteral(Universe::TYPE),
                    },
                }),
                output: Box::new(TypedTerm {
                    universe: Universe::TYPE.succ(),
                    ty: TypedTermKind::SortLiteral(Universe::TYPE),
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
                            universe: Universe::TYPE.succ().succ(),
                            ty: TypedTermKind::SortLiteral(Universe::TYPE.succ()),
                            term: TypedTermKind::SortLiteral(Universe::TYPE),
                        },
                    }),
                    output: Box::new(TypedTerm {
                        universe: Universe::TYPE.succ(),
                        ty: TypedTermKind::SortLiteral(Universe::TYPE),
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
        assert_eq!(
            TypedTermKind::BoundVariable {
                index: 0,
                name: Identifier::dummy()
            }
            .replace_binder(
                0,
                &TypedTerm {
                    universe: Universe::TYPE.succ(),
                    ty: TypedTermKind::SortLiteral(Universe::TYPE),
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
                        universe: Universe::TYPE.succ(),
                        ty: TypedTermKind::SortLiteral(Universe::TYPE),
                        term: TypedTermKind::AdtName(AdtIndex(0)),
                    }
                }),
                output: Box::new(TypedTerm {
                    universe: Universe::TYPE.succ(),
                    ty: TypedTermKind::SortLiteral(Universe::TYPE),
                    term: TypedTermKind::BoundVariable {
                        index: 1,
                        name: Identifier::dummy()
                    }
                }),
            }
            .replace_binder(
                0,
                &TypedTerm {
                    universe: Universe::TYPE.succ(),
                    ty: TypedTermKind::SortLiteral(Universe::TYPE),
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
                        universe: Universe::TYPE.succ(),
                        ty: TypedTermKind::SortLiteral(Universe::TYPE),
                        term: TypedTermKind::AdtName(AdtIndex(0)),
                    }
                }),
                output: Box::new(TypedTerm {
                    universe: Universe::TYPE.succ(),
                    ty: TypedTermKind::SortLiteral(Universe::TYPE),
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
                        universe: Universe::TYPE.succ(),
                        ty: TypedTermKind::SortLiteral(Universe::TYPE),
                        term: TypedTermKind::AdtName(AdtIndex(0)),
                    }
                }),
                output: Box::new(TypedTerm {
                    universe: Universe::TYPE.succ(),
                    ty: TypedTermKind::SortLiteral(Universe::TYPE),
                    term: TypedTermKind::BoundVariable {
                        index: 2,
                        name: Identifier::dummy()
                    }
                }),
            }
            .replace_binder(
                0,
                &TypedTerm {
                    universe: Universe::TYPE.succ(),
                    ty: TypedTermKind::SortLiteral(Universe::TYPE),
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
                        universe: Universe::TYPE.succ(),
                        ty: TypedTermKind::SortLiteral(Universe::TYPE),
                        term: TypedTermKind::AdtName(AdtIndex(0)),
                    }
                }),
                output: Box::new(TypedTerm {
                    universe: Universe::TYPE.succ(),
                    ty: TypedTermKind::SortLiteral(Universe::TYPE),
                    term: TypedTermKind::BoundVariable {
                        index: 1,
                        name: Identifier::dummy()
                    }
                })
            }
        );
    }
}
