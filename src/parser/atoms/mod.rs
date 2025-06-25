pub mod whitespace;

use std::io::Write;
use crate::parser::combinators::modifiers::VerifyExt;
use crate::parser::{InternKey, ParseResult, Parser, parser, PrettyPrint, Interner, PrettyPrintContext};

pub fn str_exact(s: &str) -> impl Parser<()> {
    parser(move |input, context| {
        input
            .strip_prefix(s)
            .map(|rest| (rest, ParseResult::new(())))
    })
}

fn char() -> impl Parser<char> {
    parser(move |input, context| {
        let mut chars = input.chars();
        let c = chars.next()?;
        Some((chars.as_str(), ParseResult::new(c)))
    })
}

#[derive(Debug)]
pub struct Identifier(InternKey);

fn identifier_start() -> impl Parser<char> {
    char().verify(|c| *c == '_' || icu_properties::sets::id_start().contains(*c))
}

fn identifier_continue() -> impl Parser<char> {
    char().verify(|c| icu_properties::sets::id_continue().contains(*c))
}

pub fn identifier() -> impl Parser<Identifier> {
    parser(move |input, context| {
        let mut chars = input.char_indices();
        let (_, first) = chars.next()?;

        if !icu_properties::sets::id_start().contains(first) {
            return None;
        }

        // Get the identifier as a string slice - this spans until the first character which is not
        // in the id_continue set, or the whole input string.
        let s = chars
            .find(|(_, c)| !icu_properties::sets::id_continue().contains(*c))
            .map(|(index, _)| &input[..index])
            .unwrap_or(input);
        
        let sym = context.interner.get_or_intern(s);
        let id = Identifier(sym);
        
        Some((&input[s.len()..], ParseResult::new(id)))
    })
}

pub fn keyword(kw: &str) -> impl Parser<()> {
    parser(move |input, context| {
        let rest = input.strip_prefix(kw)?;
        let next = rest.chars().next().unwrap_or(' ');

        // The next character must not be a valid character for an identifier
        if !icu_properties::sets::id_start().contains(next) {
            Some((rest, ParseResult::new(())))
        } else {
            None
        }
    })
}

impl PrettyPrint for Identifier {
    fn pretty_print(&self, out: &mut dyn Write, context: PrettyPrintContext) -> std::io::Result<()> {
        write!(out, "{}", context.interner.resolve(self.0).unwrap())
    }
}