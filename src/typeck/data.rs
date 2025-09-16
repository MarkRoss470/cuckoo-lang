use crate::parser::PrettyPrint;
use crate::parser::ast::item::LevelParameters;
use crate::parser::ast::item::data::DataDefinition;
use crate::parser::ast::term::LevelExpr;
use crate::parser::atoms::ident::{Identifier, OwnedPath, Path};
use crate::typeck::level::Level;
use crate::typeck::term::{TypedBinder, TypedTerm, TypedTermKind};
use crate::typeck::{AdtIndex, PrettyPrintContext, TypeError, TypingContext, TypingEnvironment};
use std::io::Write;
use std::rc::Rc;

#[derive(Debug)]
pub struct Adt {
    pub header: AdtHeader,
    pub constructors: Vec<AdtConstructor>,
}

#[derive(Debug)]
pub struct AdtHeader {
    pub index: AdtIndex,
    pub name: OwnedPath,
    pub level_params: LevelParameters,
    pub parameters: Vec<TypedBinder>,
    pub family: TypedTerm,
    pub indices: Vec<TypedBinder>,
    pub sort: Rc<Level>,
}

#[derive(Debug)]
pub struct AdtConstructor {
    pub name: Identifier,
    /// The whole type of the constructor
    pub ty: TypedTerm,
    /// The inputs to the constructor
    pub params: Vec<AdtConstructorParam>,
    /// The [`indices`] of the ADT produced by the constructor
    ///
    /// [`indices`]: Adt::indices
    pub indices: Vec<TypedTerm>,
}

#[cfg_attr(test, derive(PartialEq))]
#[derive(Debug)]
pub struct AdtConstructorParam {
    pub name: Option<Identifier>,
    pub kind: AdtConstructorParamKind,
}

#[cfg_attr(test, derive(PartialEq))]
#[derive(Debug)]
pub enum AdtConstructorParamKind {
    Inductive {
        parameters: Vec<TypedBinder>,
        indices: Vec<TypedTerm>,
    },
    NonInductive(TypedTerm),
}

impl<'a> TypingEnvironment<'a> {
    pub(super) fn resolve_adt(&mut self, ast: &'a DataDefinition) -> Result<(), TypeError> {
        // Set the level parameters for this item
        self.set_level_params(&ast.level_params)?;

        let adt_index = AdtIndex(self.adts.len());
        let header = self.resolve_adt_header(ast, adt_index)?;

        // Add a stub ADT to `self.ads` so that if this ADT shows up in any errors while resolving the constructors,
        // it can be printed properly
        self.adts.push(Adt {
            header,
            constructors: vec![],
        });
        let header = &self.adts.last().unwrap().header;

        let adt_name_ty =
            TypedTerm::make_telescope(header.parameters.clone(), header.family.clone());
        // The term that the ADT name should resolve to
        let adt_name_value = TypedTerm {
            level: adt_name_ty.check_is_ty()?,
            ty: adt_name_ty.term,
            term: TypedTermKind::AdtName(adt_index),
        };
        // Resolve the constructors
        let constructors = self.resolve_adt_constructors(&ast, header, &adt_name_value)?;

        // Fully add the ADT to the environment
        self.root.insert_namespace(ast.name.borrow());
        self.root
            .insert(ast.name.borrow(), ast.level_params.clone(), adt_name_value)?;
        let adt_namespace = self.root.resolve_namespace_mut(ast.name.borrow())?;
        for (i, constructor) in constructors.iter().enumerate() {
            adt_namespace.insert(
                Path::from_id(&constructor.name),
                ast.level_params.clone(),
                TypedTerm {
                    level: constructor.ty.check_is_ty()?,
                    ty: constructor.ty.term.clone(),
                    term: TypedTermKind::AdtConstructor(adt_index, i),
                },
            )?;
        }
        self.adts.last_mut().unwrap().constructors = constructors;

        // let eliminator = self.generate_eliminator(self.adts.last().unwrap());
        // let adt_namespace = self.root.resolve_namespace_mut(ast.name.borrow())?;
        // adt_namespace.insert(Path::from_id(&self.ast.interner.kw_rec()), eliminator)?;

        // Remove the level parameters from the context
        self.clear_level_params();

        Ok(())
    }

    fn resolve_adt_header(
        &mut self,
        ast: &'a DataDefinition,
        index: AdtIndex,
    ) -> Result<AdtHeader, TypeError> {
        let root = TypingContext::Root(self);

        let mut parameters = Vec::new();
        for param in &ast.parameters {
            let context = root.with_binders(&parameters);
            let ty = context.resolve_term(&param.ty)?;
            parameters.push(TypedBinder {
                name: param.name,
                ty,
            })
        }
        let context = root.with_binders(&parameters);

        let family = context.resolve_term(&ast.family)?;

        let Ok(_) = family.check_is_ty() else {
            return Err(TypeError::NotASortFamily(family));
        };

        // Resolve the type's family as a telescope
        let (indices, out) = family.clone().decompose_telescope();
        // Check that the output of the telescope is a sort
        let Ok(sort) = out.term.check_is_sort() else {
            return Err(TypeError::NotASortFamily(family));
        };

        // TODO: check that the ADT's level is at least as large as the levels of all parameters,
        // and larger than the levels of all indices

        Ok(AdtHeader {
            index,
            name: ast.name.clone(),
            level_params: ast.level_params.clone(),
            parameters,
            family,
            indices,
            sort,
        })
    }

    fn resolve_adt_constructors(
        &self,
        ast: &DataDefinition,
        header: &AdtHeader,
        adt_name_value: &TypedTerm,
    ) -> Result<Vec<AdtConstructor>, TypeError> {
        // Set up a TypingContext to resolve the constructor types in
        let adt_name_binder = TypedBinder {
            name: Some(ast.name.last()),
            ty: adt_name_value.get_type(),
        };
        let root = TypingContext::Root(self);
        let context = root.with_binder(&adt_name_binder);
        let context = context.with_binders(&header.parameters);

        let mut constructors = Vec::new();

        for constructor in &ast.constructors {
            let ty = context
                .resolve_term(&constructor.telescope)?
                // The binder which refers to the ADT name comes after all the parameter names
                .replace_binder(header.parameters.len(), adt_name_value);

            let constructor = self.resolve_adt_constructor(constructor.name, &ty, header)?;

            constructors.push(constructor);
        }

        Ok(constructors)
    }

    fn resolve_adt_constructor(
        &self,
        name: Identifier,
        ty: &TypedTerm,
        header: &AdtHeader,
    ) -> Result<AdtConstructor, TypeError> {
        // Check that the constructor is actually a type, and decompose it as a telescope
        ty.check_is_ty()?;
        let (parameters, output) = ty.clone().decompose_telescope();

        // Check that the output type is legal
        let arguments = self.resolve_adt_constructor_output(output, name, &parameters, header)?;

        // TODO: check that the levels of parameters are legal

        let mut processed_params = Vec::new();

        for param in parameters {
            processed_params.push(self.resolve_adt_constructor_param(name, header.index, param)?);
        }

        Ok(AdtConstructor {
            name,
            ty: ty.clone(),
            params: processed_params,
            indices: arguments,
        })
    }

    fn resolve_adt_constructor_param(
        &self,
        name: Identifier,
        adt_index: AdtIndex,
        param: TypedBinder,
    ) -> Result<AdtConstructorParam, TypeError> {
        let (parameters, output) = param.ty.clone().decompose_telescope();
        let (f, args) = output.decompose_application_stack();

        // If f is the ADT being constructed, then this is an inductive parameter
        let param_kind = match f.term {
            TypedTermKind::AdtName(id) if id == adt_index => {
                for binder in &parameters {
                    binder.ty.term.forbid_references_to_adt(adt_index)?;
                }
                for arg in &args {
                    arg.term.forbid_references_to_adt(adt_index)?;
                }

                // TODO: check ADT parameters are the same as definition

                AdtConstructorParamKind::Inductive {
                    parameters,
                    indices: args,
                }
            }

            // If the type has any other form, then just check that it doesn't contain the ADT at all
            _ => {
                param.ty.term.forbid_references_to_adt(adt_index)?;

                AdtConstructorParamKind::NonInductive(param.ty)
            }
        };

        Ok(AdtConstructorParam {
            name: param.name,
            kind: param_kind,
        })
    }

    fn resolve_adt_constructor_output(
        &self,
        output: TypedTerm,
        name: Identifier,
        constructor_params: &[TypedBinder],
        header: &AdtHeader,
    ) -> Result<Vec<TypedTerm>, TypeError> {
        // Decompose the output of the telescope as a series of applications.
        // The underlying function should be the name of the ADT being constructed
        let (f, arguments) = output.decompose_application_stack();

        // Check that the underlying function is the correct ADT name
        match f.term {
            TypedTermKind::AdtName(id) if id == header.index => (),

            _ => {
                return Err(TypeError::IncorrectConstructorResultantType {
                    name,
                    found: f,
                    expected: header.index,
                });
            }
        }

        // Check that the parameters are exactly the same as in the ADT header
        for (i, _) in header.parameters.iter().enumerate() {
            let expected = TypedTermKind::BoundVariable {
                // The binders for ADT parameters come after the constructor parameters,
                // and earlier parameters have higher indices
                index: constructor_params.len() + header.parameters.len()
                    - i
                    - 1,
                name,
            };

            // TODO: check this without cloning
            if !arguments[i].term.clone().def_eq(expected.clone()) {
                return Err(TypeError::MismatchedAdtParameter {
                    found: arguments[i].clone(),
                    expected,
                });
            }
        }

        // Check that the arguments do not include references to the current ADT
        for argument in &arguments {
            argument.term.forbid_references_to_adt(header.index)?;
        }

        Ok(arguments)
    }

    fn generate_eliminator(&self, adt: &Adt) -> TypedTerm {
        // let mut params = Vec::new();
        //
        // let motive_out = TypedTerm {
        //     level: (),
        //     ty: (),
        //     term: (),
        // };

        todo!()
    }
}

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for Adt {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext<'a>,
    ) -> std::io::Result<()> {
        self.header.pretty_print(out, context)?;

        for constructor in &self.constructors {
            constructor.pretty_print(out, context)?;
        }

        writeln!(out)
    }
}

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for AdtHeader {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext<'a>,
    ) -> std::io::Result<()> {
        write!(out, "data ")?;
        self.name.pretty_print(out, context.interner())?;
        self.level_params.pretty_print(out, context.interner())?;

        for parameter in &self.parameters {
            write!(out, " ")?;
            parameter.pretty_print(out, context)?;
        }

        write!(out, " : ")?;

        for index in &self.indices {
            index.pretty_print(out, context)?;
            write!(out, " -> ")?;
        }
        TypedTermKind::SortLiteral(self.sort.clone()).pretty_print(out, context)?;

        writeln!(out, " where")
    }
}

impl<'a> PrettyPrint<PrettyPrintContext<'a>> for AdtConstructor {
    fn pretty_print(
        &self,
        out: &mut dyn Write,
        context: PrettyPrintContext<'a>,
    ) -> std::io::Result<()> {
        write!(out, "  ")?;
        self.name.pretty_print(out, context.interner())?;
        write!(out, " : ")?;
        self.ty.term.pretty_print(out, context)?;
        writeln!(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::ast::item::Item;
    use crate::typeck::level::LevelArgs;
    use crate::typeck::tests::setup_env;

    macro_rules! resolve_adt {
        ($source: expr, $ast: ident, $env: ident, $res: ident, ) => {
            let file = crate::parse_file($source).unwrap();
            let Some(Item::DataDefinition($ast)) = &file.items.last() else {
                panic!();
            };
            let mut $env = TypingEnvironment::new(&file);
            $env.resolve_adt($ast).expect("ADT should have resolved");
            let $res = &$env.adts[0];
        };
    }

    #[test]
    fn test_resolve_adt_nat() {
        resolve_adt!(
            "data Nat : Type where
              | zero : Nat
              | succ : Nat -> Nat",
            ast,
            env,
            res,
        );

        let id_nat = ast.name.clone();

        // Check the header
        assert_eq!(ast.name, res.header.name);
        assert_eq!(res.header.level_params, LevelParameters::new(&[]));
        assert!(res.header.parameters.is_empty());
        assert!(res.header.indices.is_empty());
        assert_eq!(res.header.sort, Level::constant(1));
        assert_eq!(
            res.header.family,
            TypedTerm::sort_literal(Level::constant(1))
        );

        // Check the constructors
        let [zero, succ] = res.constructors.as_slice() else {
            panic!("Wrong number of constructors");
        };

        let nat = TypedTerm {
            level: Level::constant(2),
            ty: TypedTermKind::SortLiteral(Level::constant(1)),
            term: TypedTermKind::AdtName(res.header.index),
        };

        assert!(zero.params.is_empty());
        assert!(zero.indices.is_empty());
        assert_eq!(zero.ty, nat.clone());

        assert_eq!(
            succ.params,
            vec![AdtConstructorParam {
                name: None,
                kind: AdtConstructorParamKind::Inductive {
                    parameters: vec![],
                    indices: vec![]
                }
            }]
        );
        assert!(succ.indices.is_empty());
        assert_eq!(
            succ.ty,
            TypedTerm::make_pi_type(
                TypedBinder {
                    name: None,
                    ty: nat.clone()
                },
                nat.clone()
            )
        );

        // Check the generated constants
        let type_constructor = env
            .resolve_path(id_nat.borrow(), &LevelArgs::default())
            .unwrap();

        assert_eq!(
            type_constructor,
            TypedTerm {
                level: Level::constant(2),
                ty: TypedTermKind::SortLiteral(Level::constant(1)),
                term: TypedTermKind::AdtName(res.header.index),
            }
        );

        let zero_const = env
            .resolve_path(
                id_nat.clone().append(zero.name).borrow(),
                &LevelArgs::default(),
            )
            .unwrap();

        assert_eq!(
            zero_const,
            TypedTerm {
                level: Level::constant(1),
                ty: TypedTermKind::AdtName(res.header.index),
                term: TypedTermKind::AdtConstructor(res.header.index, 0),
            }
        );

        let succ_const = env
            .resolve_path(
                id_nat.clone().append(succ.name).borrow(),
                &LevelArgs::default(),
            )
            .unwrap();

        assert_eq!(
            succ_const,
            TypedTerm {
                level: Level::constant(1),
                ty: TypedTerm::make_pi_type(
                    TypedBinder {
                        name: None,
                        ty: nat.clone()
                    },
                    nat.clone()
                )
                .term,
                term: TypedTermKind::AdtConstructor(res.header.index, 1),
            }
        );

        // TODO: check the type of the recursor
    }

    #[test]
    fn test_resolve_adt_list() {
        resolve_adt!(
            "data List.{u} (T : Type u) : Type u where
              | nil  : List T
              | cons : T -> List T -> List T",
            ast,
            env,
            res,
        );

        let [id_u] = ast.level_params.0.as_slice() else {
            panic!("Wrong number of level parameters");
        };
        let id_t = ast.parameters[0].name.unwrap();

        assert_eq!(ast.name, res.header.name);
        assert_eq!(res.header.level_params, LevelParameters::new(&[*id_u]));
        let type_u = Level::parameter(0, *id_u).succ();
        assert_eq!(
            res.header.parameters,
            vec![TypedBinder {
                name: Some(id_t),
                ty: TypedTerm::sort_literal(type_u.clone())
            }]
        );
        assert_eq!(res.header.indices, vec![]);
        assert_eq!(res.header.sort, type_u);
        assert_eq!(
            res.header.family,
            TypedTerm::sort_literal(Level::parameter(0, *id_u).succ())
        );

        // TODO: check the type of the recursor
    }

    #[test]
    fn test_resolve_adt_eq() {
        resolve_adt!(
            "data Eq.{u} (T : Sort u) (x : T) : T -> Prop where
              | refl : Eq T x x
            ",
            ast,
            env,
            res,
        );

        let [id_u] = ast.level_params.0.as_slice() else {
            panic!("Wrong number of level parameters");
        };
        let id_t = ast.parameters[0].name.unwrap();
        let id_x = ast.parameters[1].name.unwrap();

        // TODO: check the type of the recursor
    }

    #[test]
    fn test_resolve_adt_constructor_output() {
        setup_env!(env);

        let name = OwnedPath::from_id(Identifier::dummy_val(0));
        //
        // let header = AdtHeader {
        //     index: AdtIndex(0),
        //     name: name.clone(),
        //     level_params: Default::default(),
        //     parameters: vec![],
        //     family: TypedTerm {},
        //     indices: vec![],
        //     sort: Rc::new(Level::Zero),
        // };
        //
        // env.resolve_adt_constructor_output();
    }
}
