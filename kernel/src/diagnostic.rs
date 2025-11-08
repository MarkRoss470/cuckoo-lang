//! The [`KernelError`] type

use crate::typeck::{PrettyPrintContext, TypeError};
use common::PrettyPrint;
use parser::error::ParseDiagnostic;
use std::io::Write;

/// An error which can occur while type-checking code
#[derive(Debug)]
pub enum KernelError {
    /// The syntax of the code was incorrect
    Parse(ParseDiagnostic),
    /// The code was not type-correct
    Type(Box<TypeError>),
}

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for KernelError {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext<'a>,
    ) -> std::io::Result<()> {
        match self {
            KernelError::Parse(d) => d.pretty_print(out, context),
            KernelError::Type(e) => e.pretty_print(out, context),
        }
    }
}
