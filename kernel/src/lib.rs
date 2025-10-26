use crate::diagnostic::KernelError;
use crate::typeck::{PrettyPrintContext, TypedTerm, TypingEnvironment};
use common::PrettyPrint;
use parser::SourceFile;
use parser::error::{ParseDiagnostic, ParseDiagnosticKind};
use std::io::Write;

mod diagnostic;
mod typeck;

pub use typeck::TypingEnvironmentConfig as KernelConfig;

#[derive(Debug)]
pub struct KernelEnvironment(TypingEnvironment);

impl KernelEnvironment {
    pub fn new() -> Self {
        Self(TypingEnvironment::new())
    }

    pub fn load(&mut self, source: &SourceFile) -> Result<(), KernelError> {
        self.0.load(source)
    }

    #[cfg(any(test, feature = "test-utils"))]
    pub fn check_str(&mut self, source: &str) -> Result<(), KernelError> {
        self.0.load_str(source)
    }

    pub fn config(&self) -> &KernelConfig {
        &self.0.config
    }

    pub fn config_mut(&mut self) -> &mut KernelConfig {
        &mut self.0.config
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

        match &self.kind {
            CouldNotResolveImportStatement(e) => writeln!(out, "{e}"),

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
    use std::fs;
    use std::path::Path;
    use test_each_file::test_each_path;

    fn test_case([file, out]: [&Path; 2]) {
        let mut env = TypingEnvironment::new();
        let out_content = fs::read(out).unwrap();
        let out_content = String::from_utf8(out_content).unwrap();

        match env.load(&SourceFile::from_file(file.to_path_buf()).unwrap()) {
            Ok(()) => {
                assert_eq!(
                    out_content, "success",
                    "Typechecking should not have succeeded"
                )
            }
            Err(e) => {
                let mut s = Vec::new();
                e.pretty_print(&mut s, PrettyPrintContext::new(&env))
                    .unwrap();
                let s = String::from_utf8(s).unwrap();

                assert_eq!(out_content, s, "Error did not match file content");
            }
        }
    }

    test_each_path! {for ["ck", "out"] in "kernel/tests" => test_case}
}
