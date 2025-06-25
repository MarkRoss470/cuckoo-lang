use crate::parser::combinators::sequence::CombineExt;
use crate::parser::{Parser, parser, todo};

fn ignore_val<T, P: Parser<T>>(p: P) -> impl Parser<()> {
    parser(move |input, context| {
        p.parse(input, context)
            .map(|(rest, res)| (rest, res.with_value(())))
    })
}

pub trait IgnoreValExt<T>: Parser<T> {
    fn ignore_val(self) -> impl Parser<()>;
}

impl<T, P: Parser<T>> IgnoreValExt<T> for P {
    fn ignore_val(self) -> impl Parser<()> {
        ignore_val(self)
    }
}

fn verify<T, P: Parser<T>, F: Fn(&T) -> bool>(p: P, f: F) -> impl Parser<T> {
    parser(move |input, context| {
        let (rest, res) = p.parse(input, context)?;

        if f(&res.value) {
            Some((rest, res))
        } else {
            None
        }
    })
}

pub trait VerifyExt<T>: Parser<T> {
    fn verify<F: Fn(&T) -> bool>(self, f: F) -> impl Parser<T>;
}

impl<T, P: Parser<T>> VerifyExt<T> for P {
    fn verify<F: Fn(&T) -> bool>(self, f: F) -> impl Parser<T> {
        verify(self, f)
    }
}

fn map<T, U, P: Parser<T>, F: Fn(T) -> U>(p: P, f: F) -> impl Parser<U> {
    parser(move |input, context| {
        let (rest, res) = p.parse(input, context)?;
        let res = res.map(&f);
        Some((rest, res))
    })
}

pub trait MapExt<T>: Parser<T> {
    fn map<U, F: Fn(T) -> U>(self, f: F) -> impl Parser<U>;
}

impl<T, P: Parser<T>> MapExt<T> for P {
    fn map<U, F: Fn(T) -> U>(self, f: F) -> impl Parser<U> {
        map(self, f)
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

impl<T, P: Parser<T>> DebugExt<T> for P {
    fn debug(self, message: &str) -> impl Parser<T> {
        parser(move |input, context| {
            let start: String = input.chars().take(15).collect();
            println!("{message}: {start:?}");
            self.parse(input, context)
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
