//! # Kernel
//!
//! The `kernel` crate implements the core logic of the Cuckoo language. It is designed to be
//! small and simple, to avoid bugs that lead to unsoundness. More complex features such as type
//! inference and recursive definitions will instead be implemented in the `elaborator` crate.

#![warn(clippy::missing_docs_in_private_items)]
#![warn(missing_docs)]

use crate::diagnostic::KernelError;
use crate::typeck::{PrettyPrintContext, TypedTerm, TypingEnvironment};
use common::PrettyPrint;
use parser::SourceFile;
use parser::error::{ParseDiagnostic, ParseDiagnosticKind};
use std::io::Write;

mod diagnostic;
mod typeck;

pub use typeck::TypingEnvironmentConfig as KernelConfig;
#[cfg(feature = "track-stats")]
pub use typeck::TypingEnvironmentStats as KernelStats;

/// A typing environment which stores the ADTs, axioms, and value definitions which have been
/// defined so far.
#[derive(Debug, Default)]
pub struct KernelEnvironment(TypingEnvironment);

impl KernelEnvironment {
    /// Constructs a new [`KernelEnvironment`] with no defined items.
    pub fn new() -> Self {
        Self::default()
    }

    /// Typechecks a file. Any names defined by the file's contents will be stored in `self` and
    /// can be used by future files.
    pub fn load(&mut self, source: &SourceFile) -> Result<(), KernelError> {
        self.0.load(source)
    }

    /// Runs [`load`] on content from a string
    ///
    /// [`load`]: KernelEnvironment::load
    #[cfg(any(test, feature = "test-utils"))]
    pub fn load_str(&mut self, source: &str) -> Result<(), KernelError> {
        self.0.load_str(source)
    }

    /// Gets a reference to the kernel's configuration
    pub fn config(&self) -> &KernelConfig {
        &self.0.config
    }

    /// Gets a mutable reference to the kernel's configuration
    pub fn config_mut(&mut self) -> &mut KernelConfig {
        &mut self.0.config
    }

    /// Gets a copy of the kernel's stats
    #[cfg(feature = "track-stats")]
    pub fn stats(&self) -> KernelStats {
        self.0.stats.clone()
    }

    /// Pretty prints the environment to `stdout`
    pub fn pretty_print(&self) {
        self.0.pretty_print();
    }

    /// Pretty prints a term to `stdout` followed by a newline
    pub fn pretty_println_term(&self, term: &KernelTerm) {
        self.0.pretty_println_val(&term.0);
    }

    /// Pretty prints an error to `stdout` followed by a newline
    pub fn pretty_println_error(&self, error: &KernelError) {
        match error {
            KernelError::Parse(pe) => self.0.pretty_println_val(pe),
            KernelError::Type(te) => self.0.pretty_println_val(te.as_ref()),
        }
    }
}

/// A term which has been type-checked by the kernel
#[derive(Debug)]
pub struct KernelTerm(TypedTerm);

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for ParseDiagnostic {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        _context: PrettyPrintContext<'a>,
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
        }
    }
}

#[cfg(test)]
mod integration_tests {
    use super::*;
    use std::fs;
    use std::ops::Add;
    use std::path::Path;
    use test_each_file::test_each_path;

    fn test_case([file, out]: [&Path; 2]) {
        let mut env = TypingEnvironment::default();
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

                if out_content == "REPLACE" {
                    fs::write(out, &s).expect("Should have been able to overwrite expected output");
                    // Panic because this doesn't really mean the test succeeded
                    panic!("Overwrote output file")
                } else {
                    assert_eq!(out_content, s, "Error did not match file content");
                }
            }
        }
    }

    // #[test]
    #[expect(dead_code)]
    /// A wrapper around `test_case` which makes it easier to debug one test
    fn test_one() {
        let stem = "tests/typing/def_eq/lambdas_2";

        test_case([
            Path::new(&stem.to_string().add(".ck")),
            Path::new(&stem.to_string().add(".out")),
        ]);
    }

    test_each_path! {for ["ck", "out"] in "kernel/tests" => test_case}
}
