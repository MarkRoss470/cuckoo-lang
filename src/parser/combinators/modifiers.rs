use crate::parser::combinators::tuples::HeterogeneousTupleExt;
use crate::parser::{ParseResult, Parser, parser};
use std::fmt::Debug;

pub trait IgnoreValExt: Parser {
    fn with_value<T: Clone>(self, t: T) -> impl Parser<Output = T>;
    fn ignore_value(self) -> impl Parser<Output = ()>;
}

impl<P: Parser> IgnoreValExt for P {
    fn with_value<T: Clone>(self, t: T) -> impl Parser<Output = T> {
        parser(move |input, context| {
            self.parse(input, context)
                .map(|(rest, res)| (rest, res.with_value(t.clone())))
        })
    }
    fn ignore_value(self) -> impl Parser<Output = ()> {
        self.with_value(())
    }
}

pub trait OptionalExt: Parser {
    fn optional(self) -> impl Parser<Output = Option<Self::Output>>;
    fn optional_or_else(self, t: impl Fn() -> Self::Output) -> impl Parser<Output = Self::Output>;
    fn optional_or_default(self) -> impl Parser<Output = Self::Output>
    where
        Self::Output: Default;
}

impl<P: Parser> OptionalExt for P {
    fn optional(self) -> impl Parser<Output = Option<Self::Output>> {
        parser(move |input, context| match self.parse(input, context) {
            None => Some((input, ParseResult::new(None))),
            Some((rest, res)) => Some((rest, res.map(Some))),
        })
    }

    fn optional_or_else(self, t: impl Fn() -> Self::Output) -> impl Parser<Output = Self::Output> {
        self.optional().map(move |v| v.unwrap_or_else(&t))
    }

    fn optional_or_default(self) -> impl Parser<Output = Self::Output>
    where
        Self::Output: Default,
    {
        self.optional_or_else(Default::default)
    }
}

pub trait VerifyExt: Parser {
    fn verify<F: Fn(&Self::Output) -> bool>(self, f: F) -> impl Parser<Output = Self::Output>;
}

impl<P: Parser> VerifyExt for P {
    fn verify<F: Fn(&Self::Output) -> bool>(self, f: F) -> impl Parser<Output = Self::Output> {
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

pub trait MapExt: Parser {
    fn map<U, F: Fn(Self::Output) -> U>(self, f: F) -> impl Parser<Output = U>;
}

impl<P: Parser> MapExt for P {
    fn map<U, F: Fn(Self::Output) -> U>(self, f: F) -> impl Parser<Output = U> {
        parser(move |input, context| {
            let (rest, res) = self.parse(input, context)?;
            let res = res.map(&f);
            Some((rest, res))
        })
    }
}

pub trait VerifyStrExt: Parser {
    fn verify_str<F: Fn(&str) -> bool>(self, f: F) -> impl Parser<Output = Self::Output>;
}

impl<P: Parser> VerifyStrExt for P {
    fn verify_str<F: Fn(&str) -> bool>(self, f: F) -> impl Parser<Output = Self::Output> {
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

pub trait MapStrExt: Parser {
    fn map_str<U, F: Fn(&str) -> U>(self, f: F) -> impl Parser<Output = U>;
}

impl<P: Parser> MapStrExt for P {
    fn map_str<U, F: Fn(&str) -> U>(self, f: F) -> impl Parser<Output = U> {
        self.reparse(parser(move |input, _| {
            Some(("", ParseResult::new(f(input))))
        }))
    }
}

pub trait ReparseExt: Parser {
    /// Runs the parser `self`, then runs the parser `q` on the input consumed by `self`.
    /// `q` must consume all its input, otherwise the whole parser will fail to match.
    fn reparse<U, Q: Parser<Output = U>>(self, q: Q) -> impl Parser<Output = U>;
}

impl<P: Parser> ReparseExt for P {
    fn reparse<U, Q: Parser<Output = U>>(self, q: Q) -> impl Parser<Output = U> {
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

pub trait InBoxExt: Parser {
    fn in_box(self) -> impl Parser<Output = Box<Self::Output>>;
}

impl<P: Parser> InBoxExt for P {
    fn in_box(self) -> impl Parser<Output = Box<Self::Output>> {
        self.map(Box::new)
    }
}

pub trait DebugExt: Parser {
    fn debug(self, message: &str) -> impl Parser<Output = Self::Output>;
}

impl<P: Parser<Output: Debug>> DebugExt for P {
    fn debug(self, message: &str) -> impl Parser<Output = Self::Output> {
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

pub trait ThenIgnoreExt: Parser {
    fn then_ignore<Q: Parser>(self, q: Q) -> impl Parser<Output = Self::Output>;
}

impl<P: Parser> ThenIgnoreExt for P {
    fn then_ignore<Q: Parser>(self, q: Q) -> impl Parser<Output = Self::Output> {
        (self, q).combine(|(t, _)| t)
    }
}
