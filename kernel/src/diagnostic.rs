use parser::error::ParseDiagnostic;
use crate::typeck::TypeError;

#[cfg_attr(test, derive(PartialEq))]
#[derive(Debug, Clone)]
pub enum KernelError {
    Parse(ParseDiagnostic),
    Type(TypeError),
}
