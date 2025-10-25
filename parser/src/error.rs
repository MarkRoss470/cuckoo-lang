use crate::{Source, SourceFile, SourceFromFileError};
use std::env;
use std::fmt::{Display, Formatter, write};
use std::rc::Rc;

#[cfg_attr(any(test, feature = "test-utils"), derive(PartialEq))]
#[derive(Debug, Clone)]
pub enum ParseDiagnosticKind {
    UnclosedBracket,

    MalformedItem,

    MissingBinderName,

    MissingLambdaBinder,
    MissingLambdaArrow,
    MissingLambdaBody,
}

#[derive(Debug, Copy, Clone)]
pub struct SourceLocation {
    pub byte_offset: usize,
    pub line: usize,
    pub column: usize,
}

#[derive(Debug, Clone)]
pub struct Span {
    pub source: Rc<Source>,
    pub start: SourceLocation,
    pub end: SourceLocation,
}

impl SourceLocation {
    fn min(self, other: Self) -> Self {
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
    pub fn start_point(&self) -> Span {
        Span {
            source: self.source.clone(),
            start: self.start,
            end: self.start,
        }
    }

    pub fn end_point(&self) -> Span {
        Span {
            source: self.source.clone(),
            start: self.end,
            end: self.end,
        }
    }

    pub fn union(&self, other: &Self) -> Self {
        assert_eq!(self.source, other.source);
        Self {
            source: self.source.clone(),
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }
}

impl Display for Source {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Source::File(p) => {
                if let Ok(current_dir) = env::current_dir()
                    && let Ok(relative) = p.strip_prefix(&current_dir)
                {
                    write!(f, "{}", relative.display())
                } else {
                    write!(f, "{}", p.display())
                }
            }
            Source::TestSource => write!(f, "<test source>"),
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
        write!(f, "{} {}-{}", self.source, self.start, self.end)
    }
}

#[cfg_attr(any(test, feature = "test-utils"), derive(PartialEq))]
#[derive(Debug, Clone)]
pub struct ParseDiagnostic {
    pub location: Span,
    pub kind: ParseDiagnosticKind,
}

#[cfg(any(test, feature = "test-utils"))]
impl PartialEq for Span {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

#[cfg(any(test, feature = "test-utils"))]
impl Eq for Span {}

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
            source: Rc::new(Source::TestSource),
            start: SourceLocation::dummy(),
            end: SourceLocation::dummy(),
        }
    }
}
