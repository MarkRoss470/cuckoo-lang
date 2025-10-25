use crate::typeck::{PrettyPrintContext, TypeError};
use common::PrettyPrint;
use parser::error::ParseDiagnostic;
use std::io::Write;

#[derive(Debug)]
pub enum KernelError {
    Parse(ParseDiagnostic),
    Type(TypeError),
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
