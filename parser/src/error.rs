use std::fmt::{Display, Formatter};

#[cfg_attr(any(test, debug_assertions), derive(PartialEq))]
#[derive(Debug, Clone)]
pub enum ParseDiagnosticKind {
    UnclosedBracket,

    MalformedItem,
    
    MissingBinderName,

    MissingLambdaBinder,
    MissingLambdaArrow,
    MissingLambdaBody,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct SourceLocation {
    pub byte_offset: usize,
    pub line: usize,
    pub column: usize,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Span {
    pub start: SourceLocation,
    pub end: SourceLocation,
}

impl SourceLocation {
    fn min(self, other: Self) -> Self {
        // TODO: check the locations are in the same file
        if self.byte_offset < other.byte_offset {
            self
        } else {
            other
        }
    }
    fn max(self, other: Self) -> Self {
        // TODO: check the locations are in the same file
        if self.byte_offset > other.byte_offset {
            self
        } else {
            other
        }
    }
}

impl Span {
    pub fn start_point(self) -> Span {
        Span {
            start: self.start,
            end: self.start,
        }
    }

    pub fn end_point(self) -> Span {
        Span {
            start: self.end,
            end: self.end,
        }
    }

    pub fn point(location: SourceLocation) -> Self {
        Self {
            start: location,
            end: location,
        }
    }

    pub fn union(self, other: Self) -> Self {
        Self {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }
}

impl Display for SourceLocation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

impl Display for Span {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}-{}", self.start, self.end)
    }
}

#[cfg_attr(any(test, debug_assertions), derive(PartialEq))]
#[derive(Debug, Clone)]
pub struct ParseDiagnostic {
    pub location: Span,
    pub kind: ParseDiagnosticKind,
}

#[cfg(any(test, feature = "test-utils"))]
impl SourceLocation {
    pub fn dummy() -> Self {
        Self {
            byte_offset: 0,
            line: 0,
            column: 0,
        }
    }
}

#[cfg(any(test, feature = "test-utils"))]
impl Span {
    pub fn dummy() -> Self {
        Self {
            start: SourceLocation::dummy(),
            end: SourceLocation::dummy(),
        }
    }
}
