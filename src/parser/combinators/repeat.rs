use crate::parser::{ParseResult, Parser, parser, todo};

fn repeat_0<T, P: Parser<T>>(p: P) -> impl Parser<Vec<T>> {
    parser(move |mut input, mut context| {
        let mut result = ParseResult::new(());
        let mut values = Vec::new();

        loop {
            match p.parse(input, context.borrow()) {
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

pub trait Repeat0Ext<T>: Parser<T> {
    fn repeat_0(self) -> impl Parser<Vec<T>>;
}

impl<T, P: Parser<T>> Repeat0Ext<T> for P {
    fn repeat_0(self) -> impl Parser<Vec<T>> {
        repeat_0(self)
    }
}

fn repeat_exact<T, P: Parser<T>>(n: usize, p: P) -> impl Parser<Vec<T>> {
    parser(move |mut input, mut context| {
        let mut result = ParseResult::new(());
        let mut values = Vec::new();

        for _ in 0..n {
            match p.parse(input, context.borrow()) {
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

pub trait RepeatExactExt<T>: Parser<T> {
    fn repeat_exact(self, n: usize) -> impl Parser<Vec<T>>;
}

impl<T, P: Parser<T>> RepeatExactExt<T> for P {
    fn repeat_exact(self, n: usize) -> impl Parser<Vec<T>> {
        repeat_exact(n, self)
    }
}

fn repeat_0_while<T, P: Parser<T>, F: Fn(&T) -> bool>(p: P, f: F) -> impl Parser<Vec<T>> {
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

pub trait RepeatWhileExt<T>: Parser<T> {
    fn repeat_0_while<F: Fn(&T) -> bool>(self, f: F) -> impl Parser<Vec<T>>;
}

impl<T, P: Parser<T>> RepeatWhileExt<T> for P {
    fn repeat_0_while<F: Fn(&T) -> bool>(self, f: F) -> impl Parser<Vec<T>> {
        repeat_0_while(self, f)
    }
}

fn repeat_0_until<T, P: Parser<T>, F: Fn(&T) -> bool>(p: P, f: F) -> impl Parser<Vec<T>> {
    parser(move |mut input, mut context| {
        let mut result = ParseResult::new(());
        let mut values = Vec::new();

        loop {
            match p.parse(input, context.borrow()) {
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

pub trait RepeatUntilExt<T>: Parser<T> {
    fn repeat_0_until<F: Fn(&T) -> bool>(self, f: F) -> impl Parser<Vec<T>>;
}

impl<T, P: Parser<T>> RepeatUntilExt<T> for P {
    fn repeat_0_until<F: Fn(&T) -> bool>(self, f: F) -> impl Parser<Vec<T>> {
        repeat_0_until(self, f)
    }
}

fn repeat_1_with_separator<T, P: Parser<T>, S: Parser<()>>(p: P, s: S) -> impl Parser<Vec<T>> {
    parser(move |mut input, mut context| {
        let mut res = ParseResult::new(());
        let mut v = Vec::new();

        let (rest, res1) = p.parse(input, context.borrow())?;
        input = rest;
        v.push(res.take_errors_from(res1));

        loop {
            let Some((rest, res1)) = s.parse(input, context.borrow()) else {
                break;
            };
            let Some((rest, res2)) = p.parse(rest, context.borrow()) else {
                break;
            };

            input = rest;
            res.take_errors_from(res1);
            v.push(res.take_errors_from(res2));
        }

        Some((input, res.with_value(v)))
    })
}

pub trait Repeat1WithSeparatorExt<T>: Parser<T> {
    fn repeat_1_with_separator<S: Parser<()>>(self, s: S) -> impl Parser<Vec<T>>;
}

impl<T, P: Parser<T>> Repeat1WithSeparatorExt<T> for P {
    fn repeat_1_with_separator<S: Parser<()>>(self, s: S) -> impl Parser<Vec<T>> {
        repeat_1_with_separator(self, s)
    }
}

fn fold_1<T, P: Parser<T>, F: Fn(T, T) -> T>(p: P, f: F) -> impl Parser<T> {
    parser(move |mut input, mut context| {
        let (rest, mut res) = p.parse(input, context.borrow())?;
        input = rest;

        while let Some((rest, res1)) = p.parse(input, context.borrow()) {
            input = rest;
            let r = res.take_errors_from(res1);
            res = res.map(|l|f(l, r));
        }

        Some((input, res))
    })
}

pub trait Fold1Ext<T>: Parser<T> {
    fn fold_1<F: Fn(T, T) -> T>(self, f: F) -> impl Parser<T>;
}

impl<T, P: Parser<T>> Fold1Ext<T> for P {
    fn fold_1<F: Fn(T, T) -> T>(self, f: F) -> impl Parser<T> {
        fold_1(self, f)
    }
}