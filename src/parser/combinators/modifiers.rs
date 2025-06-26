use crate::parser::combinators::sequence::CombineExt;
use crate::parser::{ParseContext, ParseResult, Parser, parser, todo};
use std::fmt::Debug;

pub trait IgnoreValExt<T>: Parser<T> {
    fn ignore_val(self) -> impl Parser<()>;
}

impl<T, P: Parser<T>> IgnoreValExt<T> for P {
    fn ignore_val(self) -> impl Parser<()> {
        parser(move |input, context| {
            self.parse(input, context)
                .map(|(rest, res)| (rest, res.with_value(())))
        })
    }
}

pub trait VerifyExt<T>: Parser<T> {
    fn verify<F: Fn(&T) -> bool>(self, f: F) -> impl Parser<T>;
}

impl<T, P: Parser<T>> VerifyExt<T> for P {
    fn verify<F: Fn(&T) -> bool>(self, f: F) -> impl Parser<T> {
        parser(move |input, context| {
            let (rest, res) = self.parse(input, context)?;

            if f(&res.value) {
                Some((rest, res))
            } else {
                None
            }
        })
    }
}

pub trait MapExt<T>: Parser<T> {
    fn map<U, F: Fn(T) -> U>(self, f: F) -> impl Parser<U>;
}

impl<T, P: Parser<T>> MapExt<T> for P {
    fn map<U, F: Fn(T) -> U>(self, f: F) -> impl Parser<U> {
        parser(move |input, context| {
            let (rest, res) = self.parse(input, context)?;
            let res = res.map(&f);
            Some((rest, res))
        })
    }
}

pub trait VerifyStrExt<T>: Parser<T> {
    fn verify_str<F: Fn(&str) -> bool>(self, f: F) -> impl Parser<T>;
}

impl<T, P: Parser<T>> VerifyStrExt<T> for P {
    fn verify_str<F: Fn(&str) -> bool>(self, f: F) -> impl Parser<T> {
        parser(move |input, context| {
            let (rest, res) = self.parse(input, context)?;
            let parsed_str = &input[..input.len() - rest.len()];

            if f(parsed_str) {
                Some((rest, res))
            } else {
                None
            }
        })
    }
}

pub trait MapStrExt<T>: Parser<T> {
    fn map_str<U, F: Fn(&str) -> U>(self, f: F) -> impl Parser<U>;
}

impl<T, P: Parser<T>> MapStrExt<T> for P {
    fn map_str<U, F: Fn(&str) -> U>(self, f: F) -> impl Parser<U> {
        self.reparse(parser(move |input, _| {
            Some(("", ParseResult::new(f(input))))
        }))
    }
}

pub trait ReparseExt<T>: Parser<T> {
    /// Runs the parser `self`, then runs the parser `q` on the input consumed by `self`.
    /// `q` must consume all its input, otherwise the whole parser will fail to match.
    fn reparse<U, Q: Parser<U>>(self, q: Q) -> impl Parser<U>;
}

impl<T, P: Parser<T>> ReparseExt<T> for P {
    fn reparse<U, Q: Parser<U>>(self, q: Q) -> impl Parser<U> {
        parser(move |input, mut context| {
            let (rest_p, res_p) = self.parse(input, context.borrow())?;
            let parsed_str = &input[..input.len() - rest_p.len()];
            let (rest_q, res_q) = q.parse(parsed_str, context)?;

            if !rest_q.is_empty() {
                None
            } else {
                Some((rest_p, res_q.with_errors_from(res_p)))
            }
        })
    }
}

fn in_box<T, P: Parser<T>>(p: P) -> impl Parser<Box<T>> {
    p.map(Box::new)
}

pub trait InBoxExt<T>: Parser<T> {
    fn in_box(self) -> impl Parser<Box<T>>;
}

impl<T, P: Parser<T>> InBoxExt<T> for P {
    fn in_box(self) -> impl Parser<Box<T>> {
        in_box(self)
    }
}

pub trait DebugExt<T>: Parser<T> {
    fn debug(self, message: &str) -> impl Parser<T>;
}

impl<T: Debug, P: Parser<T>> DebugExt<T> for P {
    fn debug(self, message: &str) -> impl Parser<T> {
        parser(move |input, context| {
            let start: String = input.chars().take(15).collect();
            let res = self.parse(input, context);
            print!("{message}: {start:?} -> ");
            match &res {
                None => println!("no match"),
                Some((rest, res)) => {
                    let rest: String = rest.chars().take(15).collect();
                    println!("{:?}, {rest:?}", res.value)
                }
            }
            res
        })
    }
}

fn then_ignore<T, U, P: Parser<T>, Q: Parser<U>>(p: P, q: Q) -> impl Parser<T> {
    (p, q).combine(|(t, _)| t)
}

pub trait ThenIgnoreExt<T>: Parser<T> {
    fn then_ignore<U, Q: Parser<U>>(self, q: Q) -> impl Parser<T>;
}

impl<T, P: Parser<T>> ThenIgnoreExt<T> for P {
    fn then_ignore<U, Q: Parser<U>>(self, q: Q) -> impl Parser<T> {
        then_ignore(self, q)
    }
}
