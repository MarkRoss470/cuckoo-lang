use crate::Parser;
use crate::atoms::{char, intern, special_operator};
use crate::combinators::modifiers::MapExt;
use crate::combinators::modifiers::{IgnoreValExt, ReparseExt, VerifyExt, VerifyStrExt};
use crate::combinators::repeat::FinalSeparatorBehaviour::ForbidFinal;
use crate::combinators::repeat::{Repeat0Ext, Repeat1WithSeparatorExt};
use crate::combinators::tuples::{HeterogeneousTupleExt, HomogeneousTupleExt};
use common::{Identifier, Interner, PrettyPrint};
use icu_properties::props::{IdContinue, IdStart};
use icu_properties::{CodePointSetData, CodePointSetDataBorrowed};
use std::io::Write;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct OwnedPath(Vec<Identifier>);

impl OwnedPath {
    pub fn from_id(id: Identifier) -> Self {
        Self(vec![id])
    }

    pub fn borrow(&self) -> Path<'_> {
        Path(&self.0)
    }

    pub fn last(&self) -> Identifier {
        *self.0.last().unwrap()
    }

    #[allow(unused)] // Only used in tests
    pub fn append(mut self, id: Identifier) -> Self {
        self.0.push(id);
        self
    }

    pub fn prepend(mut self, id: Identifier) -> Self {
        self.0.insert(0, id);
        self
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
    "Prop", "Sort", "Type", "_", "axiom", "data", "def", "fun", "imax", "import", "max", "rec",
    "succ", "where",
];

fn identifier_start() -> impl Parser<Output = ()> {
    char()
        .verify(|&c| c == '_' || ID_START_SET.contains(c))
        .ignore_value()
}

fn identifier_continue() -> impl Parser<Output = ()> {
    char()
        .verify(|&c| c == '_' || c == '\'' || ID_CONTINUE_SET.contains(c))
        .ignore_value()
}

/// Parses an identifier, without the restriction that it can't be a keyword
fn identifier_like() -> impl Parser<Output = Identifier> {
    rec!(
        (identifier_start(), identifier_continue().repeat_0())
            .sequence()
            .reparse(intern())
            .map(Identifier)
    )
}

pub(crate) fn identifier() -> impl Parser<Output = Identifier> {
    identifier_like().verify_str(|s| !RESERVED_IDENTIFIERS.binary_search(&s).is_ok())
}

pub(crate) fn keyword(kw: &str) -> impl Parser<Output = ()> {
    debug_assert!(KNOWN_IDENTIFIERS.contains(&kw));

    identifier_like()
        .verify_str(move |s| s == kw)
        .ignore_value()
}

pub(crate) fn path() -> impl Parser<Output = OwnedPath> {
    // A path contains either identifiers or the keyword 'rec'
    rec!(
        (
            identifier(),
            identifier_like().verify_str(move |s| s == "rec"),
        )
            .alt()
            .repeat_1_with_separator(ForbidFinal, special_operator("."))
            .map(OwnedPath)
    )
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
    use crate::tests::ParserTestExt;

    #[test]
    fn test_reserved_identifiers_sorted() {
        assert!(RESERVED_IDENTIFIERS.is_sorted());
        assert!(KNOWN_IDENTIFIERS.is_sorted());
    }

    #[test]
    fn test_keywords_are_identifiers() {
        let mut interner = Interner::new();

        for kw in RESERVED_IDENTIFIERS {
            identifier_like().parse_all(kw, &mut interner);
        }
    }

    #[test]
    fn test_identifier() {
        let mut interner = Interner::new();

        let id_test = Identifier::from_str("test", &mut interner);
        let id_test_10 = Identifier::from_str("test_10", &mut interner);
        let id_underscore_test = Identifier::from_str("_test", &mut interner);
        let id_def_test = Identifier::from_str("def_test", &mut interner);

        assert_eq!(
            identifier().parse_leaving("test id", " id", &mut interner),
            id_test
        );
        assert_eq!(
            identifier().parse_leaving("test,id", ",id", &mut interner),
            id_test
        );
        assert_eq!(
            identifier().parse_leaving("test_10-id", "-id", &mut interner),
            id_test_10
        );
        assert_eq!(
            identifier().parse_leaving("_test--id", "--id", &mut interner),
            id_underscore_test
        );
        identifier().assert_no_match("10test", &mut interner);

        // Keywords aren't identifiers...
        identifier().assert_no_match("def", &mut interner);
        identifier().assert_no_match("_", &mut interner);
        // ...but identifiers can start with them
        assert_eq!(
            identifier().parse_all("def_test", &mut interner),
            id_def_test
        );
    }

    #[test]
    fn test_path() {
        let mut interner = Interner::new();

        let id_y = Identifier::from_str("y", &mut interner);
        let id_x = Identifier::from_str("x", &mut interner);
        let id_z = Identifier::from_str("z", &mut interner);

        assert_eq!(
            path().parse_leaving("x.y.z ", " ", &mut interner),
            OwnedPath(vec![id_x, id_y, id_z])
        );
        assert_eq!(
            path().parse_leaving("x .y ", " .y ", &mut interner),
            OwnedPath(vec![id_x])
        );
        assert_eq!(
            path().parse_leaving("x. ", ". ", &mut interner),
            OwnedPath(vec![id_x])
        );
        assert_eq!(
            path().parse_leaving("x.{y}", ".{y}", &mut interner),
            OwnedPath(vec![id_x])
        );
    }
}
