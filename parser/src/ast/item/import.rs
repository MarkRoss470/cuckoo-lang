use crate::ast::item::Item;
use crate::ast::parse_file;
use crate::atoms::char;
use crate::atoms::ident::keyword;
use crate::combinators::modifiers::{FlatMapExt, MapExt, ReparseExt};
use crate::combinators::modifiers::{MapStrExt, VerifyExt, WithSpanExt};
use crate::combinators::repeat::{Repeat0Ext, Repeat1Ext};
use crate::combinators::tuples::HeterogeneousTupleExt;
use crate::error::{ParseDiagnostic, ParseDiagnosticKind, Span};
use crate::{Parser, Source, SourceFile, SourceFromFileError};
use common::{Diagnostic, DiagnosticSeverity};
use std::path::PathBuf;

pub(crate) fn import_statement() -> impl Parser<Output = Vec<Item>> {
    rec!(
        (
            keyword("import"),
            char()
                .verify(|c| *c != '\n')
                .repeat_0()
                .map_str(|s| s.to_string()),
        )
            .sequence_with_whitespace()
            .with_span()
            .flat_map_with_context(|context, ((_, path), span)| {
                if path.is_empty() {
                    return (vec![], vec![]);
                }
                let path = PathBuf::from(path);

                // If the current source is a file, resolve the path relative to it
                let path = match &*context.source.source {
                    Source::File(p) => p.parent().unwrap().join(path),
                    Source::TestSource => path,
                };

                let source = match SourceFile::from_file(path) {
                    Ok(source) => source,
                    Err(e) => {
                        return (
                            vec![],
                            vec![Diagnostic {
                                value: ParseDiagnostic {
                                    location: span,
                                    kind: ParseDiagnosticKind::CouldNotResolveImportStatement(e),
                                },
                                severity: DiagnosticSeverity::Error,
                            }],
                        );
                    }
                };

                let res = parse_file(context.interner, &source);

                (res.value.items, res.diagnostics)
            })
    )
}
