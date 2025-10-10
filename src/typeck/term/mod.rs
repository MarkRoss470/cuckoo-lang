pub mod accessors;
pub mod constructors;
pub mod def_eq;
pub mod modifiers;
#[cfg(test)]
mod tests;

use crate::parser::PrettyPrint;
use crate::parser::atoms::ident::{Identifier, OwnedPath};
use crate::typeck::level::{Level, LevelArgs};
use crate::typeck::{AdtIndex, PrettyPrintContext};
use std::io::Write;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypedTerm {
    level: Level,
    ty: TypedTermKind,
    term: TypedTermKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypedTermKind(Rc<TypedTermKindInner>);

#[derive(Debug, Clone, Eq)]
enum TypedTermKindInner {
    /// The keywords `Sort n`, `Prop` or `Type n`
    SortLiteral(Level),
    /// The name of an ADT
    AdtName(AdtIndex),
    /// The name of an ADT constructor
    AdtConstructor(AdtIndex, usize),
    /// The recursor of an ADT
    AdtRecursor(AdtIndex),
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

#[derive(Debug, Clone, Eq)]
pub struct TypedBinder {
    pub name: Option<Identifier>,
    pub ty: TypedTerm,
}

impl PartialEq for TypedTermKindInner {
    fn eq(&self, other: &Self) -> bool {
        use TypedTermKindInner::*;

        match (self, other) {
            (SortLiteral(l1), SortLiteral(l2)) => l1 == l2,
            (SortLiteral(_), _) => false,
            (AdtName(a1), AdtName(a2)) => a1 == a2,
            (AdtName(_), _) => false,
            (AdtConstructor(a1, c1), AdtConstructor(a2, c2)) => a1 == a2 && c1 == c2,
            (AdtConstructor(_, _), _) => false,
            (AdtRecursor(a1), AdtRecursor(a2)) => a1 == a2,
            (AdtRecursor(_), _) => false,
            (BoundVariable { index: i1, name: _ }, BoundVariable { index: i2, name: _ }) => {
                i1 == i2
            }
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
            ) => f1 == f2 && a1 == a2,
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
            ) => b1 == b2 && o1 == o2,
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
            ) => b1 == b2 && bo1 == bo2,
            (Lambda { .. }, _) => false,
        }
    }
}

impl PartialEq for TypedBinder {
    fn eq(&self, other: &Self) -> bool {
        self.ty == other.ty
    }
}

impl TypedTerm {
    fn shallow_eq(&self, other: &Self) -> bool {
        self.ty().ptr_eq(&other.ty()) && self.term().ptr_eq(&other.term())
    }
}

impl TypedTermKindInner {
    fn shallow_eq(&self, other: &Self) -> bool {
        use TypedTermKindInner::*;

        match (self, other) {
            (SortLiteral(l1), SortLiteral(l2)) => l1.ptr_eq(l2),
            (SortLiteral(_), _) => false,
            (AdtName(a1), AdtName(a2)) => a1 == a2,
            (AdtName(_), _) => false,
            (AdtConstructor(a1, c1), AdtConstructor(a2, c2)) => a1 == a2 && c1 == c2,
            (AdtConstructor(_, _), _) => false,
            (AdtRecursor(a1), AdtRecursor(a2)) => a1 == a2,
            (AdtRecursor(_), _) => false,
            (
                BoundVariable {
                    index: i1,
                    name: n1,
                },
                BoundVariable {
                    index: i2,
                    name: n2,
                },
            ) => i1 == i2 && n1 == n2,
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
            ) => f1.shallow_eq(f2) && a1.shallow_eq(a2),
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
            ) => b1.shallow_eq(b2) && o1.shallow_eq(o2),
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
            ) => b1.shallow_eq(b2) && bo1.shallow_eq(bo2),
            (Lambda { .. }, _) => false,
        }
    }
}

impl TypedBinder {
    fn shallow_eq(&self, other: &Self) -> bool {
        self.name == other.name && self.ty.shallow_eq(&other.ty)
    }
}

impl TypedTermKind {
    fn inner(&self) -> &TypedTermKindInner {
        self.0.as_ref()
    }

    fn clone_inner(&self) -> TypedTermKindInner {
        self.0.as_ref().clone()
    }

    fn ptr_eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
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
            AdtConstructor(adt, con) => {
                let adt = context.environment.get_adt(*adt);

                adt.header.name.pretty_print(out, &context.interner())?;
                write!(out, ".")?;
                adt.constructors[*con]
                    .name
                    .pretty_print(out, &context.interner())
            }
            AdtRecursor(adt) => {
                context
                    .environment
                    .get_adt(*adt)
                    .header
                    .name
                    .pretty_print(out, &context.interner())?;
                write!(out, ".rec")
            }
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
