use crate::combinators::modifiers::WithSpanExt;
use crate::error::{ParseDiagnostic, ParseDiagnosticKind};
use crate::{ParseResult, Parser, parser};

pub trait OrErrorExt: Parser {
    fn or_error(self, error: ParseDiagnosticKind) -> impl Parser<Output = ()>;

    fn or_else_error(
        self,
        error: ParseDiagnosticKind,
        or_else: impl Parser<Output = Self::Output>,
    ) -> impl Parser<Output = Self::Output>;
}

impl<P: Parser> OrErrorExt for P {
    fn or_error(self, error: ParseDiagnosticKind) -> impl Parser<Output = ()> {
        parser(
            move |input, mut context| match self.parse(input, context.borrow()) {
                Some((rest, res)) => Some((rest, res.with_value(()))),
                None => Some((
                    input,
                    ParseResult::new(()).with_error(context.diagnostic_at(input, error.clone())),
                )),
            },
        )
    }

    fn or_else_error(
        self,
        error: ParseDiagnosticKind,
        or_else: impl Parser<Output = Self::Output>,
    ) -> impl Parser<Output = Self::Output> {
        let or_else = or_else.with_span();
        parser(
            move |input, mut context| match self.parse(input, context.borrow()) {
                Some(v) => Some(v),
                None => {
                    let (rest, res) = or_else
                        .parse(input, context.borrow())
                        .expect("Fallback parser should have matched");

                    let span = res.value.1;

                    Some((
                        rest,
                        res.map(|(v, _)| v).with_error(ParseDiagnostic {
                            location: span,
                            kind: error.clone(),
                        }),
                    ))
                }
            },
        )
    }
}
