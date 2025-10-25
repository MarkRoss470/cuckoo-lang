use crate::combinators::modifiers::{MapExt, VerifyExt};
use crate::{ParseResult, Parser, parser};
use std::iter;

pub(crate) trait Repeat0FlatteningExt: Parser<Output: IntoIterator> {
    fn repeat_0_flattening(
        self,
    ) -> impl Parser<Output = Vec<<<Self as Parser>::Output as IntoIterator>::Item>>;
}

impl<P: Parser<Output: IntoIterator>> Repeat0FlatteningExt for P {
    fn repeat_0_flattening(
        self,
    ) -> impl Parser<Output = Vec<<<Self as Parser>::Output as IntoIterator>::Item>> {
        parser(move |mut input, mut context| {
            let mut result = ParseResult::new(());
            let mut values = Vec::new();

            loop {
                if input.is_empty() {
                    break;
                }

                match self.parse(input, context.borrow()) {
                    None => break,
                    Some((rest, res)) => {
                        input = rest;
                        let iter = result.take_diagnostics_from(res);
                        for v in iter.into_iter() {
                            values.push(v);
                        }
                    }
                }
            }

            Some((input, result.with_value(values)))
        })
    }
}

pub(crate) trait Repeat0Ext: Parser {
    fn repeat_0(self) -> impl Parser<Output = Vec<Self::Output>>;
}

impl<P: Parser> Repeat0Ext for P {
    fn repeat_0(self) -> impl Parser<Output = Vec<Self::Output>> {
        self.map(|v| iter::once(v)).repeat_0_flattening()
    }
}

pub(crate) trait Repeat1Ext: Parser {
    fn repeat_1(self) -> impl Parser<Output = Vec<Self::Output>>;
}

impl<P: Parser> Repeat1Ext for P {
    fn repeat_1(self) -> impl Parser<Output = Vec<Self::Output>> {
        self.repeat_0().verify(|v| !v.is_empty())
    }
}

pub(crate) trait RepeatExactExt: Parser {
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
                        values.push(result.take_diagnostics_from(res));
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
                    values.push(result.take_diagnostics_from(res));
                }
            }
        }

        Some((input, result.with_value(values)))
    })
}

pub(crate) trait RepeatWhileExt: Parser {
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

pub(crate) trait RepeatUntilExt: Parser {
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
                        values.push(result.take_diagnostics_from(res));

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
pub(crate) enum FinalSeparatorBehaviour {
    /// Allow a final separator
    AllowFinal,
    /// Do not allow a final separator
    ForbidFinal,
}

pub(crate) trait Repeat1WithSeparatorExt: Parser {
    /// Repeats `self` at least once, separated by another src, whose output is ignored.
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
            v.push(res.take_diagnostics_from(res1));

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

                res.take_diagnostics_from(res1);
                v.push(res.take_diagnostics_from(res2));
            }

            Some((input, res.with_value(v)))
        })
    }
}

pub(crate) trait Fold1Ext: Parser {
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
                let r = res.take_diagnostics_from(res1);
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
                let r = res.take_diagnostics_from(res1);
                res = res.map(|l| f(l, r));
            }

            Some((input, res))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::atoms::ident::identifier;
    use crate::atoms::whitespace::whitespace;
    use crate::combinators::repeat::FinalSeparatorBehaviour::{AllowFinal, ForbidFinal};
    use crate::tests::ParserTestExt;
    use common::{Identifier, Interner};

    #[test]
    fn test_repeat_1_with_separator() {
        let mut interner = Interner::new();

        let id_x = Identifier::from_str("x", &mut interner);
        let id_y = Identifier::from_str("y", &mut interner);
        let id_z = Identifier::from_str("z", &mut interner);

        let p = identifier().repeat_1_with_separator(AllowFinal, whitespace());

        p.assert_no_match("", &mut interner);
        p.assert_no_match(" ", &mut interner);
        p.assert_no_match(" x", &mut interner);
        assert_eq!(p.parse_all("x", &mut interner), vec![id_x]);
        assert_eq!(p.parse_all("x ", &mut interner), vec![id_x]);
        assert_eq!(
            p.parse_all("x \ny  z --comment", &mut interner),
            vec![id_x, id_y, id_z]
        );

        let p = identifier().repeat_1_with_separator(ForbidFinal, whitespace());

        p.assert_no_match("", &mut interner);
        p.assert_no_match(" ", &mut interner);
        p.assert_no_match(" x", &mut interner);
        assert_eq!(p.parse_all("x", &mut interner), vec![id_x]);
        assert_eq!(p.parse_leaving("x ", " ", &mut interner), vec![id_x]);
        assert_eq!(
            p.parse_leaving("x \ny  z --comment", " --comment", &mut interner),
            vec![id_x, id_y, id_z]
        );
    }
}
