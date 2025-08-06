use crate::parser::ast::term::Universe;
use crate::parser::atoms::{Identifier, OwnedPath};
use crate::typeck::term::{TypedBinder, TypedTerm, TypedTermKind};

#[derive(Debug)]
pub struct Adt {
    pub name: OwnedPath,
    pub indices: Vec<TypedBinder>,
    pub sort: Universe,
    pub constructors: Vec<AdtConstructor>,
}

#[derive(Debug)]
pub struct AdtConstructor {
    pub name: Identifier,
    /// The whole type of the constructor
    pub ty: TypedTermKind,
    /// The inputs to the constructor
    pub params: Vec<AdtConstructorParam>,
    /// The [`indices`] of the ADT produced by the constructor
    ///
    /// [`indices`]: Adt::indices
    pub indices: Vec<TypedTerm>,
}

#[derive(Debug)]
pub struct AdtConstructorParam {
    pub name: Option<Identifier>,
    pub kind: AdtConstructorParamKind,
}

#[derive(Debug)]
pub enum AdtConstructorParamKind {
    Inductive {
        parameters: Vec<TypedBinder>,
        indices: Vec<TypedTerm>,
    },
    NonInductive(TypedTerm),
}