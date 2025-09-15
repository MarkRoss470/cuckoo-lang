use crate::parser::combinators::modifiers::{ThenIgnoreExt, VerifyExt};
use crate::parser::{ParseResult, Parser, parser, todo};

pub trait Repeat0Ext: Parser {
    fn repeat_0(self) -> impl Parser<Output = Vec<Self::Output>>;
}

impl<P: Parser> Repeat0Ext for P {
    fn repeat_0(self) -> impl Parser<Output = Vec<Self::Output>> {
        parser(move |mut input, mut context| {
            let mut result = ParseResult::new(());
            let mut values = Vec::new();

            loop {
                match self.parse(input, context.borrow()) {
                    None => break,
                    Some((rest, res)) => {
                        input = rest;
                        values.push(result.take_errors_from(res));
                    }
                }
            }

            Some((input, result.with_value(values)))
        })
    }
}

pub trait Repeat1Ext: Parser {
    fn repeat_1(self) -> impl Parser<Output = Vec<Self::Output>>;
}

impl<P: Parser> Repeat1Ext for P {
    fn repeat_1(self) -> impl Parser<Output = Vec<Self::Output>> {
        self.repeat_0().verify(|v|!v.is_empty())
    }
}

pub trait RepeatExactExt: Parser {
    fn repeat_exact(self, n: usize) -> impl Parser<Output = Vec<Self::Output>>;
}

impl<P: Parser> RepeatExactExt for P {
    fn repeat_exact(self, n: usize) -> impl Parser<Output = Vec<Self::Output>> {
        parser(move |mut input, mut context| {
            let mut result = ParseResult::new(());
            let mut values = Vec::new();

            for _ in 0..n {
                match self.parse(input, context.borrow()) {
                    None => return None,
                    Some((rest, res)) => {
                        input = rest;
                        values.push(result.take_errors_from(res));
                    }
                }
            }

            Some((input, result.with_value(values)))
        })
    }
}

fn repeat_0_while<T, P: Parser<Output = T>, F: Fn(&T) -> bool>(
    p: P,
    f: F,
) -> impl Parser<Output = Vec<T>> {
    parser(move |mut input, mut context| {
        let mut result = ParseResult::new(());
        let mut values = Vec::new();

        loop {
            match p.parse(input, context.borrow()) {
                None => break,
                Some((rest, res)) => {
                    if !f(&res.value) {
                        break;
                    }

                    input = rest;
                    values.push(result.take_errors_from(res));
                }
            }
        }

        Some((input, result.with_value(values)))
    })
}

pub trait RepeatWhileExt: Parser {
    fn repeat_0_while<F: Fn(&Self::Output) -> bool>(
        self,
        f: F,
    ) -> impl Parser<Output = Vec<Self::Output>>;
}

impl<P: Parser> RepeatWhileExt for P {
    fn repeat_0_while<F: Fn(&Self::Output) -> bool>(
        self,
        f: F,
    ) -> impl Parser<Output = Vec<Self::Output>> {
        repeat_0_while(self, f)
    }
}

pub trait RepeatUntilExt: Parser {
    fn repeat_0_until<F: Fn(&Self::Output) -> bool>(
        self,
        f: F,
    ) -> impl Parser<Output = Vec<Self::Output>>;
}

impl<P: Parser> RepeatUntilExt for P {
    fn repeat_0_until<F: Fn(&Self::Output) -> bool>(
        self,
        f: F,
    ) -> impl Parser<Output = Vec<Self::Output>> {
        parser(move |mut input, mut context| {
            let mut result = ParseResult::new(());
            let mut values = Vec::new();

            loop {
                match self.parse(input, context.borrow()) {
                    None => break,
                    Some((rest, res)) => {
                        input = rest;
                        values.push(result.take_errors_from(res));

                        if !f(&values.last().unwrap()) {
                            break;
                        }
                    }
                }
            }

            Some((input, result.with_value(values)))
        })
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
/// Whether to allow a separator after the last value when using [`repeat_1_with_separator`]
///
/// [`repeat_1_with_separator`]: Repeat1WithSeparatorExt::repeat_1_with_separator
pub enum FinalSeparatorBehaviour {
    /// Allow a final separator
    AllowFinal,
    /// Do not allow a final separator
    ForbidFinal,
}

pub trait Repeat1WithSeparatorExt: Parser {
    /// Repeats `self` at least once, separated by another parser, whose output is ignored.
    fn repeat_1_with_separator<S: Parser>(
        self,
        fin: FinalSeparatorBehaviour,
        s: S,
    ) -> impl Parser<Output = Vec<Self::Output>>;
}

impl<P: Parser> Repeat1WithSeparatorExt for P {
    fn repeat_1_with_separator<S: Parser>(
        self,
        fin: FinalSeparatorBehaviour,
        s: S,
    ) -> impl Parser<Output = Vec<Self::Output>> {
        parser(move |mut input, mut context| {
            let mut res = ParseResult::new(());
            let mut v = Vec::new();

            // Parse the initial value
            let (rest, res1) = self.parse(input, context.borrow())?;
            input = rest;
            v.push(res.take_errors_from(res1));

            // Parse (separator, value) pairs
            loop {
                let Some((rest, res1)) = s.parse(input, context.borrow()) else {
                    break;
                };
                // If a separator is allowed after the last value, consume the separator before parsing the value.
                if fin == FinalSeparatorBehaviour::AllowFinal {
                    input = rest;
                }

                let Some((rest, res2)) = self.parse(rest, context.borrow()) else {
                    break;
                };
                input = rest;

                res.take_errors_from(res1);
                v.push(res.take_errors_from(res2));
            }

            Some((input, res.with_value(v)))
        })
    }
}

pub trait Fold1Ext: Parser {
    fn fold_1<F: Fn(Self::Output, Self::Output) -> Self::Output>(
        self,
        f: F,
    ) -> impl Parser<Output = Self::Output>;

    fn then_fold<Q: Parser, F: Fn(Self::Output, Q::Output) -> Self::Output>(
        self,
        q: Q,
        f: F,
    ) -> impl Parser<Output = Self::Output>;
}

impl<P: Parser> Fold1Ext for P {
    fn fold_1<F: Fn(Self::Output, Self::Output) -> Self::Output>(
        self,
        f: F,
    ) -> impl Parser<Output = Self::Output> {
        parser(move |mut input, mut context| {
            let (rest, mut res) = self.parse(input, context.borrow())?;
            input = rest;

            while let Some((rest, res1)) = self.parse(input, context.borrow()) {
                input = rest;
                let r = res.take_errors_from(res1);
                res = res.map(|l| f(l, r));
            }

            Some((input, res))
        })
    }

    fn then_fold<Q: Parser, F: Fn(Self::Output, Q::Output) -> Self::Output>(
        self,
        q: Q,
        f: F,
    ) -> impl Parser<Output = Self::Output> {
        parser(move |mut input, mut context| {
            let (rest, mut res) = self.parse(input, context.borrow())?;
            input = rest;

            while let Some((rest, res1)) = q.parse(input, context.borrow()) {
                input = rest;
                let r = res.take_errors_from(res1);
                res = res.map(|l| f(l, r));
            }

            Some((input, res))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::atoms::ident::{Identifier, identifier};
    use crate::parser::atoms::whitespace::whitespace;
    use crate::parser::combinators::repeat::FinalSeparatorBehaviour::{AllowFinal, ForbidFinal};
    use crate::parser::tests::{ParseAllExt, setup_context};

    #[test]
    fn test_repeat_1_with_separator() {
        setup_context!(context);

        let id_x = Identifier::from_str("x", context.interner);
        let id_y = Identifier::from_str("y", context.interner);
        let id_z = Identifier::from_str("z", context.interner);

        let p = identifier().repeat_1_with_separator(AllowFinal, whitespace());

        assert!(p.parse("", context.borrow()).is_none());
        assert!(p.parse(" ", context.borrow()).is_none());
        assert!(p.parse(" x", context.borrow()).is_none());
        assert_eq!(p.parse_all("x", context.borrow()), vec![id_x]);
        assert_eq!(p.parse_all("x ", context.borrow()), vec![id_x]);
        assert_eq!(
            p.parse_all("x \ny  z --comment", context.borrow()),
            vec![id_x, id_y, id_z]
        );

        let p = identifier().repeat_1_with_separator(ForbidFinal, whitespace());

        assert!(p.parse("", context.borrow()).is_none());
        assert!(p.parse(" ", context.borrow()).is_none());
        assert!(p.parse(" x", context.borrow()).is_none());
        assert_eq!(p.parse_all("x", context.borrow()), vec![id_x]);
        assert_eq!(p.parse_leaving("x ", " ", context.borrow()), vec![id_x]);
        assert_eq!(
            p.parse_leaving("x \ny  z --comment", " --comment", context.borrow()),
            vec![id_x, id_y, id_z]
        );
    }
}
