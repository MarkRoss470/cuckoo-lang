use parser::ParseDiagnostic;
use crate::typeck::TypeError;

#[cfg_attr(any(test, debug_assertions), derive(PartialEq))]
#[derive(Debug, Clone)]
pub enum KernelError {
    Parse(ParseDiagnostic),
    Type(TypeError),
}
