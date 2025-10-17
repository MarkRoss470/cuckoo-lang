use std::io::Write;
use string_interner::symbol::SymbolU32;
use string_interner::{DefaultBackend, StringInterner};

pub trait PrettyPrint<C> {
    fn pretty_print(&self, out: &mut dyn Write, context: C) -> std::io::Result<()>;
}

/// The key / symbol type used to compare / look up strings in the interner
pub type InternKey = SymbolU32;

/// The parser's string interner type
#[derive(Debug)]
pub struct Interner {
    interner: StringInterner<DefaultBackend>,
}

impl Interner {
    pub fn new() -> Self {
        Self {
            interner: StringInterner::new(),
        }
    }

    pub fn get_or_intern(&mut self, string: &str) -> InternKey {
        self.interner.get_or_intern(string)
    }

    pub fn resolve(&self, symbol: InternKey) -> Option<&str> {
        self.interner.resolve(symbol)
    }
}

pub fn dummy_intern_key(value: usize) -> InternKey {
    use string_interner::Symbol;

    InternKey::try_from_usize(value).unwrap()
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum DiagnosticSeverity {
    Warning,
    Error,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Diagnostic<T> {
    pub value: T,
    pub severity: DiagnosticSeverity,
}

impl<T> Diagnostic<T> {
    pub fn error(value: T) -> Self {
        Self {
            value,
            severity: DiagnosticSeverity::Error,
        }
    }

    pub fn warning(value: T) -> Self {
        Self {
            value,
            severity: DiagnosticSeverity::Warning,
        }
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Diagnostic<U> {
        Diagnostic {
            value: f(self.value),
            severity: self.severity,
        }
    }
}

#[derive(Debug, Clone)]
pub struct WithDiagnostics<T, D> {
    pub value: T,
    pub diagnostics: Vec<Diagnostic<D>>,
}

impl<T, D> WithDiagnostics<T, D> {
    pub fn new(value: T) -> Self {
        Self {
            value,
            diagnostics: vec![],
        }
    }

    pub fn push_error(&mut self, error: D) {
        self.diagnostics.push(Diagnostic::error(error));
    }

    pub fn push_warning(&mut self, warning: D) {
        self.diagnostics.push(Diagnostic::warning(warning));
    }

    pub fn with_error(mut self, error: D) -> Self {
        self.push_error(error);
        self
    }

    pub fn with_warning(mut self, warning: D) -> Self {
        self.push_warning(warning);
        self
    }

    pub fn unwrap(self) -> T {
        assert!(self.diagnostics.is_empty());
        self.value
    }

    pub fn expect(self, msg: &str) -> T {
        assert!(self.diagnostics.is_empty(), "{msg}");
        self.value
    }

    pub fn take_diagnostics_from<U, E>(&mut self, other: WithDiagnostics<U, E>) -> U
    where
        Diagnostic<D>: From<Diagnostic<E>>,
    {
        self.diagnostics
            .extend(other.diagnostics.into_iter().map(Into::into));
        other.value
    }

    pub fn with_diagnostics_from<U, E>(mut self, other: WithDiagnostics<U, E>) -> Self
    where
        Diagnostic<D>: From<Diagnostic<E>>,
    {
        self.take_diagnostics_from(other);
        self
    }

    pub fn with_value<U>(self, value: U) -> WithDiagnostics<U, D> {
        WithDiagnostics {
            value,
            diagnostics: self.diagnostics,
        }
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> WithDiagnostics<U, D> {
        WithDiagnostics {
            value: f(self.value),
            diagnostics: self.diagnostics,
        }
    }

    pub fn map_diagnostics<E>(self, f: impl Fn(D) -> E) -> WithDiagnostics<T, E> {
        WithDiagnostics {
            value: self.value,
            diagnostics: self.diagnostics.into_iter().map(|d| d.map(&f)).collect(),
        }
    }

    pub fn flat_map<U>(self, f: impl FnOnce(T) -> WithDiagnostics<U, D>) -> WithDiagnostics<U, D> {
        let Self {
            value,
            mut diagnostics,
        } = self;

        let mut new = f(value);
        diagnostics.append(&mut new.diagnostics);

        WithDiagnostics {
            value: new.value,
            diagnostics,
        }
    }

    pub fn run<U>(&mut self, f: impl FnOnce(&mut T) -> WithDiagnostics<U, D>) {
        let mut new = f(&mut self.value);
        self.diagnostics.append(&mut new.diagnostics);
    }
}
