use crate::typeck::level::Level;
use crate::typeck::term::{TypedTerm, TypedTermKindInner};
use crate::typeck::{PrettyPrintContext, TypingEnvironment};
use common::{Identifier, PrettyPrint};
use parser::atoms::ident::Path;
use std::io::Write;

enum CheckContext<'a> {
    Root,
    Binder {
        ty: &'a TypedTerm,
        parent: &'a CheckContext<'a>,
    },
}

impl<'a> CheckContext<'a> {
    fn get_type_of_binder_inner(&self, id: usize) -> Option<&TypedTerm> {
        match self {
            CheckContext::Root => None,
            CheckContext::Binder { ty, parent } => {
                if id == 0 {
                    Some(ty)
                } else {
                    parent.get_type_of_binder_inner(id - 1)
                }
            }
        }
    }

    fn get_type_of_binder(&self, id: usize) -> Option<TypedTerm> {
        self.get_type_of_binder_inner(id)
            .map(|t| t.clone_incrementing(0, id + 1))
    }
}

impl<'a> PrettyPrint<(usize, PrettyPrintContext<'a>)> for CheckContext<'a> {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        (id, context): (usize, PrettyPrintContext),
    ) -> std::io::Result<()> {
        match self {
            CheckContext::Root => Ok(()),
            CheckContext::Binder { ty, parent } => {
                write!(out, "{id}: ")?;
                ty.pretty_print(out, context)?;
                writeln!(out)?;
                parent.pretty_print(out, (id + 1, context))
            }
        }
    }
}

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for CheckContext<'a> {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext,
    ) -> std::io::Result<()> {
        self.pretty_print(out, (0, context))
    }
}

impl TypingEnvironment {
    pub fn check_term(&self, term: &TypedTerm) {
        self.check_term_with_context(term, &CheckContext::Root);
    }

    fn check_term_with_context(&self, term: &TypedTerm, context: &CheckContext) {
        use TypedTermKindInner::*;

        // If the term has been checked before, don't check it agin
        if term.checked.get() {
            return;
        }

        if !term.get_type().is_sort_literal().is_some() {
            self.check_term_with_context(&term.get_type(), context);
        }

        let true_ty = match term.term().inner() {
            SortLiteral(l) => TypedTerm::sort_literal(l.succ(), term.span()),
            AdtName(adt, level_args) => {
                let adt_name = self.get_adt(*adt).header.name.borrow();
                self.root
                    .resolve(adt_name, level_args, term.span())
                    .unwrap()
                    .get_type()
            }
            AdtConstructor(adt, constructor, level_args) => {
                let adt = self.get_adt(*adt);
                let adt_name = adt.header.name.borrow();
                let constructor_name = adt.constructors[*constructor].name;
                let adt_ns = self.root.resolve_namespace(adt_name, term.span()).unwrap();
                adt_ns
                    .resolve(Path::from_id(&constructor_name), level_args, term.span())
                    .unwrap()
                    .get_type()
            }
            AdtRecursor(adt, level_args) => {
                let adt = self.get_adt(*adt);
                let adt_name = adt.header.name.borrow();
                let adt_ns = self.root.resolve_namespace(adt_name, term.span()).unwrap();
                adt_ns
                    .resolve(
                        Path::from_id(&Identifier::from_str(
                            "rec",
                            &mut self.interner.borrow_mut(),
                        )),
                        level_args,
                        term.span(),
                    )
                    .unwrap()
                    .get_type()
            }
            Axiom(axiom, level_args) => self.get_axiom(*axiom).ty.instantiate(level_args),
            BoundVariable { index, name: _ } => match context.get_type_of_binder(*index).clone() {
                None => {
                    println!("Binders:");
                    self.pretty_println_val(context);
                    panic!("Term referenced bound variable with index {index}, which is too large.")
                }
                Some(t) => t,
            },
            Application { function, argument } => {
                self.check_term_with_context(function, context);
                self.check_term_with_context(argument, context);

                let function_ty = self.reduce_to_whnf(function.get_type());
                let (binder, output) = function_ty.is_pi_type().unwrap();

                assert!(self.def_eq(binder.ty, argument.get_type()));

                output.replace_binder(0, argument)
            }
            PiType { binder, output } => {
                self.check_term_with_context(&binder.ty, context);
                self.check_term_with_context(
                    output,
                    &CheckContext::Binder {
                        ty: &binder.ty,
                        parent: context,
                    },
                );

                TypedTerm::sort_literal(
                    Level::smart_imax(
                        &binder.ty.check_is_ty().unwrap(),
                        &output.check_is_ty().unwrap(),
                    ),
                    term.span(),
                )
            }
            Lambda { binder, body } => {
                self.check_term_with_context(&binder.ty, context);
                self.check_term_with_context(
                    body,
                    &CheckContext::Binder {
                        ty: &binder.ty,
                        parent: context,
                    },
                );

                TypedTerm::make_pi_type(binder.clone(), body.get_type(), term.span())
            }
        };

        if !term.level.def_eq(&true_ty.check_is_ty().unwrap())
            || !self.def_eq(term.get_type(), true_ty.clone())
        {
            println!("Term:");
            self.pretty_println_val_with_proofs(term);
            println!("Actual type:");
            self.pretty_println_val(&term.get_type());
            println!("Expected type:");
            self.pretty_println_val(&true_ty);
            println!("Binders:");
            self.pretty_println_val(context);

            panic!("Invalid term found")
        }

        // Cache that the term has been checked
        term.checked.set(true);
    }
}
