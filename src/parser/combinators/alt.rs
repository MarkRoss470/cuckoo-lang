use crate::parser::{ParseContext, ParseResult, Parser, parser};

/// A helper trait for the [`alt`] function. Is implemented for tuples where all the members are [`Parser`]s.
pub trait AltExt<T> {
    /// Runs the contained parsers, returning the result of the first successful one, or `None`.
    fn alt(self) -> impl Parser<T>;
}

/// Implements the [`AltExt`] trait for a tuple, given a list of generic type parameter names
macro_rules! alt_impl {
    // Takes a list of generic type parameter names and expands to an implementation for the generic tuple with those type parameters
    ($($type_param: ident)*) => {

        impl<T, $($type_param),*> AltExt<T> for ($($type_param,)*)
        // Each item of the tuple has an `Alt<T>` bound
        where $($type_param: Parser<T>),* {
            fn alt(self) -> impl Parser<T> {
                #![allow(non_snake_case)] // We are using generic parameter names as variable names for macro magic

                // Destructure tuple of parsers into variables with the same names as their types to be able to use them without needing the tuple index
                let ($($type_param,)*) = self;

                $crate::parser::parser(
                    move |input, mut context| {
                        // Check each expanded item in turn
                        $(if let Some(out) = $type_param.parse(input, context.borrow()) { return Some(out) };)*
                        // If none parsed, return none
                        None
                    }
                )
            }
        }
    };
}

/// Implements the [`AltExt`] trait for tuples of increasing arity
macro_rules! alt_impl_multiple {
    () => {};

    ($first: ident $($rest: ident)*) => {
        alt_impl!($first $($rest)*);

        alt_impl_multiple!($($rest)*);
    };
}

alt_impl_multiple!(A B C D E F G H I J K L M N O P);
