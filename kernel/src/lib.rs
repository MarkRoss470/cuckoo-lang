use crate::diagnostic::KernelError;
use crate::typeck::{PrettyPrintContext, TypeError, TypedTerm, TypingEnvironment};
use common::PrettyPrint;
use parser::ParseDiagnostic;
use parser::ast::parse_file;
use std::io::Write;

mod diagnostic;
mod typeck;

#[derive(Debug)]
pub struct KernelEnvironment(TypingEnvironment);

impl KernelEnvironment {
    pub fn new() -> Self {
        Self(TypingEnvironment::new())
    }

    pub fn check_str(&mut self, source: &str) -> Result<(), KernelError> {
        let res = parse_file(&mut self.0.interner.borrow_mut(), source);
        if let Some(e) = res.diagnostics.into_iter().next() {
            return Err(KernelError::Parse(e.value));
        }

        self.0.resolve_file(&res.value).map_err(KernelError::Type)
    }

    pub fn pretty_print(&self) {
        self.0.pretty_print();
    }

    pub fn pretty_println_term(&self, term: &KernelTerm) {
        self.0.pretty_println_val(&term.0);
    }

    pub fn pretty_println_error(&self, error: &KernelError) {
        match error {
            KernelError::Parse(pe) => self.0.pretty_println_val(pe),
            KernelError::Type(te) => self.0.pretty_println_val(te),
        }
    }
}

#[derive(Debug)]
pub struct KernelTerm(TypedTerm);

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for ParseDiagnostic {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext<'a>,
    ) -> std::io::Result<()> {
        match self {
            _ => Ok(()),
        }
    }
}
