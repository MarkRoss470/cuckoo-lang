use crate::diagnostic::KernelError;
use crate::typeck::{PrettyPrintContext, TypedTerm, TypingEnvironment};
use common::PrettyPrint;
use parser::ast::parse_file;
use parser::error::{ParseDiagnostic, ParseDiagnosticKind};
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
        if !res.diagnostics.is_empty() {
            return Err(KernelError::Parse(res.diagnostics[0].value.clone()));
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
        use ParseDiagnosticKind::*;

        write!(out, "Syntax Error at {}: ", self.location)?;

        match self.kind {
            UnclosedBracket => writeln!(out, "Unclosed bracket"),
            MalformedItem => writeln!(out, "Malformed item"),
            MissingBinderName => writeln!(out, "Missing name in binder"),
            MissingLambdaBinder => writeln!(out, "Missing binder for lambda expression"),
            MissingLambdaArrow => writeln!(out, "Missing arrow in lambda expression"),
            MissingLambdaBody => writeln!(out, "Missing body of lambda expression"),

            #[expect(unreachable_patterns)]
            _ => todo!(),
        }
    }
}

#[cfg(test)]
mod integration_tests {
    use super::*;
    use test_each_file::test_each_file;

    fn test_case([file, out]: [&str; 2]) {
        let mut env = TypingEnvironment::new();
        let ast = parse_file(&mut env.interner.borrow_mut(), file).unwrap();

        let res = env.resolve_file(&ast);

        match res {
            Ok(()) => {
                assert_eq!(out, "success", "Typechecking should not have succeeded")
            }
            Err(e) => {
                let mut s = Vec::new();
                e.pretty_print(&mut s, PrettyPrintContext::new(&env))
                    .unwrap();
                let s = String::from_utf8(s).unwrap();

                assert_eq!(out, s, "Error did not match file content");
            }
        }
    }

    test_each_file! { for ["ck", "out"] in "./kernel/tests" => test_case }
}
