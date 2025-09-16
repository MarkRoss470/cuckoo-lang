use crate::parser::atoms::{char, intern, special_operator};
use crate::parser::combinators::modifiers::MapExt;
use crate::parser::combinators::modifiers::{IgnoreValExt, ReparseExt, VerifyExt, VerifyStrExt};
use crate::parser::combinators::repeat::FinalSeparatorBehaviour::ForbidFinal;
use crate::parser::combinators::repeat::{Repeat0Ext, Repeat1WithSeparatorExt};
use crate::parser::combinators::tuples::{HeterogeneousTupleExt, HomogeneousTupleExt};
use crate::parser::{InternKey, Interner, Parser, PrettyPrint};
use icu_properties::props::{IdContinue, IdStart};
use icu_properties::{CodePointSetData, CodePointSetDataBorrowed};
use std::io::Write;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Identifier(pub(in crate::parser) InternKey);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct OwnedPath(Vec<Identifier>);

impl OwnedPath {
    pub fn from_id(id: Identifier) -> Self {
        Self(vec![id])
    }

    pub fn borrow(&self) -> Path {
        Path(&self.0)
    }

    pub fn last(&self) -> Identifier {
        *self.0.last().unwrap()
    }

    pub fn append(mut self, id: Identifier) -> Self {
        self.0.push(id);
        self
    }

    pub fn prepend(mut self, id: Identifier) -> Self {
        self.0.insert(0, id);
        self
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Path<'a>(&'a [Identifier]);

impl<'a> Path<'a> {
    pub fn from_id(id: &'a Identifier) -> Self {
        Self(core::slice::from_ref(id))
    }

    pub fn split_first(&self) -> (Identifier, Option<Path<'a>>) {
        match self.0 {
            [] => panic!("Empty path"),
            [id] => (*id, None),
            [id, rest @ ..] => (*id, Some(Path(rest))),
        }
    }

    pub fn to_owned(&self) -> OwnedPath {
        OwnedPath(self.0.to_vec())
    }
}

const ID_START_SET: CodePointSetDataBorrowed = CodePointSetData::new::<IdStart>();
const ID_CONTINUE_SET: CodePointSetDataBorrowed = CodePointSetData::new::<IdContinue>();

/// Sequences of characters which would be valid identifiers but are reserved for other purposes
const RESERVED_IDENTIFIERS: &[&str] = &[
    "Prop", "Sort", "Type", "_", "data", "def", "fun", "rec", "where",
];
/// Identifiers which have special meaning in some context
const KNOWN_IDENTIFIERS: &[&str] = &[
    "Prop", "Sort", "Type", "_", "data", "def", "fun", "imax", "max", "rec", "succ", "where",
];

fn identifier_start() -> impl Parser<Output = ()> {
    char()
        .verify(|&c| c == '_' || ID_START_SET.contains(c))
        .ignore_value()
}

fn identifier_continue() -> impl Parser<Output = ()> {
    char()
        .verify(|&c| c == '_' || ID_CONTINUE_SET.contains(c))
        .ignore_value()
}

/// Parses an identifier, without the restriction that it can't be a keyword
fn identifier_like() -> impl Parser<Output = Identifier> {
    (identifier_start(), identifier_continue().repeat_0())
        .sequence()
        .reparse(intern())
        .map(Identifier)
}

pub fn identifier() -> impl Parser<Output = Identifier> {
    identifier_like().verify_str(|s| !RESERVED_IDENTIFIERS.binary_search(&s).is_ok())
}

pub fn keyword(kw: &str) -> impl Parser<Output = ()> {
    debug_assert!(KNOWN_IDENTIFIERS.contains(&kw));

    identifier_like()
        .verify_str(move |s| s == kw)
        .ignore_value()
}

pub fn path() -> impl Parser<Output = OwnedPath> {
    // A path contains either identifiers or the keyword 'rec'
    (
        identifier(),
        identifier_like().verify_str(move |s| s == "rec"),
    )
        .alt()
        .repeat_1_with_separator(ForbidFinal, special_operator("."))
        .map(OwnedPath)
}

impl<'a> PrettyPrint<&'a Interner> for Identifier {
    fn pretty_print(&self, out: &mut dyn Write, context: &'a Interner) -> std::io::Result<()> {
        write!(out, "{}", context.resolve(self.0).unwrap())
    }
}

impl<'a> PrettyPrint<&'a Interner> for OwnedPath {
    fn pretty_print(&self, out: &mut dyn Write, context: &'a Interner) -> std::io::Result<()> {
        let mut ids = self.0.iter();
        ids.next().unwrap().pretty_print(out, context)?;

        for id in ids {
            write!(out, ".")?;
            id.pretty_print(out, context)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::tests::{ParseAllExt, setup_context};

    impl Identifier {
        pub fn from_str(str: &str, interner: &mut Interner) -> Self {
            Self(interner.get_or_intern(str))
        }

        pub fn dummy() -> Self {
            use string_interner::Symbol;

            Self(InternKey::try_from_usize(0).unwrap())
        }

        pub fn dummy_val(v: usize) -> Self {
            use string_interner::Symbol;

            Self(InternKey::try_from_usize(v).unwrap())
        }
    }

    #[test]
    fn test_reserved_identifiers_sorted() {
        assert!(RESERVED_IDENTIFIERS.is_sorted());
        assert!(KNOWN_IDENTIFIERS.is_sorted());
    }

    #[test]
    fn test_keywords_are_identifiers() {
        setup_context!(context);

        for kw in RESERVED_IDENTIFIERS {
            identifier_like().parse_all(kw, context.borrow());
        }
    }

    #[test]
    fn test_identifier() {
        setup_context!(context);

        let id_test = Identifier::from_str("test", context.interner);
        let id_test_10 = Identifier::from_str("test_10", context.interner);
        let id_underscore_test = Identifier::from_str("_test", context.interner);

        assert_eq!(
            identifier().parse_leaving("test id", " id", context.borrow()),
            id_test
        );
        assert_eq!(
            identifier().parse_leaving("test,id", ",id", context.borrow()),
            id_test
        );
        assert_eq!(
            identifier().parse_leaving("test_10-id", "-id", context.borrow()),
            id_test_10
        );
        assert_eq!(
            identifier().parse_leaving("_test--id", "--id", context.borrow()),
            id_underscore_test
        );
        assert!(identifier().parse("10test", context.borrow()).is_none());

        // Keywords aren't identifiers
        assert!(identifier().parse("def", context.borrow()).is_none());
        assert!(identifier().parse("_", context.borrow()).is_none());
    }

    #[test]
    fn test_path() {
        setup_context!(context);

        let id_x = Identifier::from_str("x", context.interner);
        let id_y = Identifier::from_str("y", context.interner);
        let id_z = Identifier::from_str("z", context.interner);

        assert_eq!(
            path().parse_leaving("x.y.z ", " ", context.borrow()),
            OwnedPath(vec![id_x, id_y, id_z])
        );
        assert_eq!(
            path().parse_leaving("x .y ", " .y ", context.borrow()),
            OwnedPath(vec![id_x])
        );
        assert_eq!(
            path().parse_leaving("x. ", ". ", context.borrow()),
            OwnedPath(vec![id_x])
        );
        assert_eq!(
            path().parse_leaving("x.{y}", ".{y}", context.borrow()),
            OwnedPath(vec![id_x])
        );
    }
}
