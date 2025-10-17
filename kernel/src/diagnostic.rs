use crate::parser::ParseDiagnostic;
use crate::typeck::TypeError;

#[cfg_attr(any(test, debug_assertions), derive(PartialEq))]
#[derive(Debug, Clone)]
pub enum KernelDiagnostic {
    Parse(ParseDiagnostic),
    Type(TypeError),
}
