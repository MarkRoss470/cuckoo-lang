use crate::atoms::whitespace::SurroundWhitespaceExt;
use crate::combinators::modifiers::MapExt;
use crate::{ParseResult, Parser};

pub(crate) trait HeterogeneousTupleExt {
    /// A tuple type made up of the output types of all the parsers in the tuple
    type OutputsTuple;

    /// Runs the contained parsers, returning the result of each. If any individual src returns `None`, so will the combined src.
    fn sequence(self) -> impl Parser<Output = Self::OutputsTuple>;

    /// Runs all the contained parsers in sequence and combines their output using the given function
    fn combine<U, F: Fn(Self::OutputsTuple) -> U>(self, f: F) -> impl Parser<Output = U>;

    /// Runs the contained parsers, returning the result of each. If any individual src returns `None`, so will the combined src.
    fn sequence_with_whitespace(self) -> impl Parser<Output = Self::OutputsTuple>;

    /// Runs all the contained parsers in sequence and combines their output using the given function, allowing for whitespace before each src.
    fn combine_with_whitespace<U, F: Fn(Self::OutputsTuple) -> U>(
        self,
        f: F,
    ) -> impl Parser<Output = U>;
}

/// Implements the [`HeterogeneousTupleExt`] trait for a tuple, given a list of generic type parameter names
macro_rules! heterogeneous_tuple_impl {
    // Takes a list of generic type parameter names and expands to an implementation for the generic tuple with those type parameters
    ($($parser_param: ident)*) => {
        // We are using generic parameter names as variable names for macro magic
        #[allow(non_snake_case)]

        // Generic impl over all data and src types
        impl<$($parser_param),*> HeterogeneousTupleExt for ($($parser_param,)*)

        // Each item of the tuple has a `Parser` bound
        where $($parser_param: Parser),*
        {
            type OutputsTuple = ($($parser_param::Output,)*);

            fn sequence(self) -> impl Parser<Output = Self::OutputsTuple> {
                // Destructure tuple of parsers into variables with the same names as their types to be able to use them without needing the tuple index
                let ($($parser_param,)*) = self;

                $crate::parser(
                    move |input, mut context| {
                        let mut res = ParseResult::new(());

                        // Run each src in turn, putting the output in a new variable with the same name as the src type
                        $(
                            let (input, $parser_param) = $parser_param.parse(input, context.borrow())?;
                            let $parser_param = res.take_diagnostics_from($parser_param);
                        )*

                        // Combine the variables into a src output
                        Some((input, res.with_value(($($parser_param,)*))))
                    }
                )
            }

            fn combine<U, Func: Fn(Self::OutputsTuple) -> U>(self, f: Func) -> impl Parser<Output = U> {
                self.sequence().map(f)
            }

            fn sequence_with_whitespace(self) -> impl Parser<Output = Self::OutputsTuple> {
                let ($($parser_param,)*) = self;

                let p = ($($parser_param.surround_whitespace(),)*);

                p.sequence()
            }

            fn combine_with_whitespace<U, Func: Fn(Self::OutputsTuple) -> U>(self, f: Func) -> impl Parser<Output = U> {
                let ($($parser_param,)*) = self;

                let p = ($($parser_param.surround_whitespace(),)*);

                p.combine(f)
            }
        }
    };
}

/// Implements the [`SequenceExt`] trait for tuples of increasing arity
macro_rules! heterogeneous_tuple_impl_multiple {
    () => {};

    ($first_parser: ident $($rest: ident)*) => {
        heterogeneous_tuple_impl!($first_parser $($rest)*);

        heterogeneous_tuple_impl_multiple!($($rest)*);
    };
}

heterogeneous_tuple_impl_multiple!(A B C D E F G H I J K L M N O P);

pub(crate) trait HomogeneousTupleExt<T> {
    fn alt(self) -> impl Parser<Output = T>;
}

/// Implements the [`HomogeneousTupleExt`] trait for a tuple, given a list of generic type parameter names
macro_rules! homogeneous_tuple_impl {
    // Takes a list of generic type parameter names and expands to an implementation for the generic tuple with those type parameters
    ($($type_param: ident)*) => {

        // We are using generic parameter names as variable names for macro magic
        #[allow(non_snake_case)]

        // Generic impl over all data and src types
        impl<T, $($type_param),*> HomogeneousTupleExt<T> for ($($type_param,)*)

        // Each item of the tuple has a `Parser<T>` bound
        where $($type_param: Parser<Output = T>),*
        {
            fn alt(self) -> impl Parser<Output = T> {

                // Destructure tuple of parsers into variables with the same names as their types to be able to use them without needing the tuple index
                let ($($type_param,)*) = self;

                $crate::parser(
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

/// Implements the [`HomogeneousTupleExt`] trait for tuples of increasing arity
macro_rules! homogeneous_tuple_impl_multiple {
    () => {};

    ($first: ident $($rest: ident)*) => {
        homogeneous_tuple_impl!($first $($rest)*);

        homogeneous_tuple_impl_multiple!($($rest)*);
    };
}

homogeneous_tuple_impl_multiple!(A B C D E F G H I J K L M N O P);
