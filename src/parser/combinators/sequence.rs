use crate::parser::combinators::modifiers::MapExt;
use crate::parser::{ParseContext, ParseResult, Parser, parser};

pub trait SequenceExt<T> {
    /// Runs the contained parsers, returning the result of each. If any individual parser returns `None`, so will the combined parser.
    fn sequence(self) -> impl Parser<T>;
}

/// Implements the [`SequenceExt`] trait for a tuple, given a list of generic type parameter names
macro_rules! sequence_impl {
    // Takes a list of generic type parameter names and expands to an implementation for the generic tuple with those type parameters
    ($($type_param: ident $parser_param: ident)*) => {
        impl<$($type_param, $parser_param),*> SequenceExt<($($type_param,)*)> for ($($parser_param,)*)

        // Each item of the tuple has an `Alt<T>` bound
        where $($parser_param: Parser<$type_param>),* {
            fn sequence(self) -> impl Parser<($($type_param,)*)> {
                #![allow(non_snake_case)] // We are using generic parameter names as variable names for macro magic

                // Destructure tuple of parsers into variables with the same names as their types to be able to use them without needing the tuple index
                let ($($parser_param,)*) = self;

                $crate::parser::parser(
                    move |input, mut context| {
                        let mut res = ParseResult::new(());

                        // Check each expanded item in turn
                        $(
                            let (input, $type_param) = $parser_param.parse(input, context.borrow())?;
                            let $type_param = res.take_errors_from($type_param);
                        )*

                        Some((input, res.with_value(($($type_param,)*))))
                    }
                )
            }
        }
    };
}

/// Implements the [`SequenceExt`] trait for tuples of increasing arity
macro_rules! seqence_impl_multiple {
    () => {};

    ($first_type: ident $first_parser: ident $($rest: ident)*) => {
        sequence_impl!($first_type $first_parser $($rest)*);

        seqence_impl_multiple!($($rest)*);
    };
}

seqence_impl_multiple!(TA PA TB PB TC PC TD PD TE PE TF PF TG PG TH PH TI PI TJ PJ TK PK TL PL TM PM TN PN TO PO TP PP);

pub trait CombineExt<T> {
    fn combine<U, F: Fn(T) -> U>(self, f: F) -> impl Parser<U>;
}

impl<T, P: SequenceExt<T>> CombineExt<T> for P {
    fn combine<U, F: Fn(T) -> U>(self, f: F) -> impl Parser<U> {
        self.sequence().map(f)
    }
}
