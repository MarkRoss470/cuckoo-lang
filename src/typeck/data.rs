use crate::parser::PrettyPrint;
use crate::parser::ast::item::LevelParameters;
use crate::parser::ast::item::data::DataDefinition;
use crate::parser::atoms::ident::{Identifier, OwnedPath, Path};
use crate::typeck::level::Level;
use crate::typeck::term::{TypedBinder, TypedTerm, TypedTermKind};
use crate::typeck::{AdtIndex, PrettyPrintContext, TypeError, TypingContext, TypingEnvironment};
use std::io::Write;
use std::rc::Rc;

#[derive(Debug)]
pub struct AdtHeader {
    pub index: AdtIndex,
    pub name: OwnedPath,
    pub level_params: LevelParameters,
    pub parameters: Vec<TypedBinder>,
    /// The type's family, i.e. everything in the header after the colon. This does not include the
    /// ADT's parameters, but it may reference them as bound variables.
    pub family: TypedTerm,
    /// The indices of the ADT's family
    pub indices: Vec<TypedBinder>,
    /// The level in which the ADT lives
    pub sort: Rc<Level>,
    /// Whether the ADT is a proposition
    pub is_prop: bool,
}

#[derive(Debug)]
pub struct Adt {
    pub header: AdtHeader,
    pub constructors: Vec<AdtConstructor>,
    /// Whether the ADT's recursor should allow eliminating to types at any level. This is true of
    /// non-propositions, and 'subsingleton' propositions with only one constructor where all the
    /// constructor's non-recursive non-proposition parameters are mentioned in the output type.
    /// This is because all values of a proposition type are equal, so they can only soundly
    /// eliminate to non-Prop types when the proposition type is guaranteed to only have at most
    /// one value.
    pub is_large_eliminating: bool,
}

impl AdtHeader {
    fn type_constructor(&self) -> TypedTerm {
        TypedTerm::value_of_type(
            TypedTermKind::AdtName(self.index),
            TypedTerm::make_telescope(self.parameters.clone(), self.family.clone()),
        )
    }

    fn constructor(&self, index: usize, constructor: &AdtConstructor) -> TypedTerm {
        TypedTerm::adt_constructor(
            self.index,
            index,
            TypedTerm::make_telescope(self.parameters.clone(), constructor.ty.clone()),
        )
    }
}

impl Adt {
    // Calculates and stores whether the ADT is large eliminating
    fn calculate_large_eliminating(&mut self) {
        self.is_large_eliminating = !self.header.is_prop || self.is_subsingleton();
    }

    fn is_subsingleton(&self) -> bool {
        // If the ADT has no constructors, it is subsingleton
        if self.constructors.is_empty() {
            return true;
        }
        // If the ADT has more than one constructor, it is not subsingleton
        if self.constructors.len() > 1 {
            return false;
        }

        let constructor = self.constructors.first().unwrap();

        // Check that each non-recursive parameter of the constructor is either a proposition,
        // or is mentioned in the constructor's indices
        for (i, parameter) in constructor.params.iter().rev().enumerate() {
            if let AdtConstructorParamKind::NonInductive(ty) = &parameter.kind {
                let is_prop = ty.level.def_eq(&Level::zero());
                let is_referenced = constructor
                    .indices
                    .iter()
                    .any(|t| t.term.references_bound_variable(i));

                if !(is_prop || is_referenced) {
                    return false;
                }
            }
        }

        true
    }
}

#[derive(Debug)]
pub struct AdtConstructor {
    pub name: Identifier,
    /// The whole type of the constructor, not including the ADT parameters
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

        // Resolve the header
        let adt_index = AdtIndex(self.adts.len());
        let header = self.resolve_adt_header(ast, adt_index)?;

        // Add a stub ADT to `self.ads` so that if this ADT shows up in any errors while resolving the constructors,
        // it can be printed properly
        self.adts.push(Adt {
            header,
            constructors: vec![],
            is_large_eliminating: false,
        });
        let header = &self.adts.last().unwrap().header;

        // Resolve the constructors
        let constructors = self.resolve_adt_constructors(&ast, header)?;
        let adt = self.adts.last_mut().unwrap();
        adt.constructors = constructors;

        // Calculate whether the ADT is large eliminating
        adt.calculate_large_eliminating();

        // Add the ADT's constants to the namespace
        self.register_last_adt()?;

        // Remove the level parameters from the context
        self.clear_level_params();

        Ok(())
    }

    /// Creates the constants associated with the last ADT in [`self.adts`] - the type constructor,
    /// constructors, and recursor.
    ///
    /// [`self.adts`]: TypingEnvironment::adts
    fn register_last_adt(&mut self) -> Result<(), TypeError> {
        let adt = self.adts.last().unwrap();
        let name = adt.header.name.borrow();
        let level_parameters = adt.header.level_params.clone();

        // Create the ADT's namespace
        self.root.insert_namespace(name);

        // Create the type constructor constant
        self.root.insert(
            name,
            level_parameters.clone(),
            adt.header.type_constructor(),
        )?;

        // Create the constructor constants
        let adt_namespace = self.root.resolve_namespace_mut(name)?;
        for (i, constructor) in adt.constructors.iter().enumerate() {
            adt_namespace.insert(
                Path::from_id(&constructor.name),
                level_parameters.clone(),
                adt.header.constructor(i, constructor), // TypedTerm::adt_constructor(adt.header.index, i, constructor.ty.clone()),
            )?;
        }

        // Create the recursor constants
        // let eliminator = self.generate_eliminator(self.adts.last().unwrap());
        // let adt_namespace = self.root.resolve_namespace_mut(ast.name.borrow())?;
        // adt_namespace.insert(Path::from_id(&self.ast.interner.kw_rec()), eliminator)?;

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

        // Check that the ADT is either always in `Prop` or always not in `Prop`
        let is_prop = if sort.def_eq(&Level::zero()) {
            true
        } else if sort.is_geq(&Level::constant(1)) {
            false
        } else {
            return Err(TypeError::MayOrMayNotBeProp(sort));
        };

        Ok(AdtHeader {
            index,
            name: ast.name.clone(),
            level_params: ast.level_params.clone(),
            parameters,
            family,
            indices,
            sort,
            is_prop,
        })
    }

    fn resolve_adt_constructors(
        &self,
        ast: &DataDefinition,
        header: &AdtHeader,
    ) -> Result<Vec<AdtConstructor>, TypeError> {
        let type_constructor = header.type_constructor();

        // Set up a TypingContext to resolve the constructor types in
        let adt_name_binder = TypedBinder {
            name: Some(ast.name.last()),
            ty: type_constructor.get_type(),
        };
        let root = TypingContext::Root(self);
        let context = root.with_binder(&adt_name_binder);
        let context = context.with_binders(&header.parameters);

        let mut constructors = Vec::new();

        for constructor in &ast.constructors {
            let ty = context
                .resolve_term(&constructor.telescope)?
                // The binder which refers to the ADT name comes after all the parameter names
                .replace_binder(header.parameters.len(), &type_constructor);

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

        // Check that the levels of parameters are legal.
        // This doesn't matter for Prop types as parameters for those can be any level.
        if !header.is_prop {
            for param in &parameters {
                self.check_adt_parameter_levels(param, &header.sort)?;
            }
        }

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

    fn check_adt_parameter_levels(
        &self,
        param: &TypedBinder,
        adt_sort: &Rc<Level>,
    ) -> Result<(), TypeError> {
        if !adt_sort.is_geq(&param.level()) {
            Err(TypeError::InvalidConstructorParameterLevel {
                ty: param.ty.clone(),
                adt_level: adt_sort.clone(),
            })
        } else {
            Ok(())
        }
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
                index: constructor_params.len() + header.parameters.len() - i - 1,
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
    use crate::typeck::tests::{assert_type_error, setup_env};
    use crate::typeck::TypeError::LevelArgumentGivenForLocalVariable;

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
        assert_eq!(res.header.is_prop, false);
        assert_eq!(res.is_large_eliminating, true);

        // Check the constructors
        let [zero, succ] = res.constructors.as_slice() else {
            panic!("Wrong number of constructors");
        };

        let nat = TypedTerm::adt_name(
            res.header.index,
            TypedTerm::sort_literal(Level::constant(1)),
        );

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

        assert_eq!(type_constructor, nat);

        let zero_const = env
            .resolve_path(
                id_nat.clone().append(zero.name).borrow(),
                &LevelArgs::default(),
            )
            .unwrap();

        assert_eq!(
            zero_const,
            TypedTerm::adt_constructor(res.header.index, 0, nat.clone())
        );

        let succ_const = env
            .resolve_path(
                id_nat.clone().append(succ.name).borrow(),
                &LevelArgs::default(),
            )
            .unwrap();

        assert_eq!(
            succ_const,
            TypedTerm::adt_constructor(
                res.header.index,
                1,
                TypedTerm::make_pi_type(
                    TypedBinder {
                        name: None,
                        ty: nat.clone()
                    },
                    nat.clone()
                )
            )
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
        let id_list = ast.name.clone();

        let level_u = Level::parameter(0, *id_u);
        let type_u = TypedTerm::sort_literal(level_u.succ());

        // Check the header
        assert_eq!(ast.name, res.header.name);
        assert_eq!(res.header.level_params, LevelParameters::new(&[*id_u]));
        assert_eq!(
            res.header.parameters,
            vec![TypedBinder {
                name: Some(id_t),
                ty: type_u.clone()
            }]
        );
        assert_eq!(res.header.indices, vec![]);
        assert_eq!(res.header.sort, level_u.succ());
        assert_eq!(res.header.family, type_u.clone());
        assert_eq!(res.header.is_prop, false);
        assert_eq!(res.is_large_eliminating, true);

        // Check the constructors
        let [nil, cons] = res.constructors.as_slice() else {
            panic!("Wrong number of constructors");
        };

        assert!(nil.params.is_empty());
        assert_eq!(
            nil.indices,
            vec![TypedTerm::bound_variable(0, id_t, type_u.clone())]
        );

        assert_eq!(
            cons.params,
            vec![
                AdtConstructorParam {
                    name: None,
                    kind: AdtConstructorParamKind::NonInductive(TypedTerm::bound_variable(
                        0,
                        id_t,
                        type_u.clone()
                    ))
                },
                AdtConstructorParam {
                    name: None,
                    kind: AdtConstructorParamKind::Inductive {
                        parameters: vec![],
                        indices: vec![TypedTerm::bound_variable(1, id_t, type_u.clone())]
                    }
                }
            ]
        );
        assert_eq!(
            cons.indices,
            vec![TypedTerm::bound_variable(2, id_t, type_u.clone())]
        );

        let args_u = LevelArgs(vec![level_u.clone()]);

        // Check the generated constants
        let list_ty = TypedTerm::make_pi_type(
            TypedBinder {
                name: Some(id_t),
                ty: type_u.clone(),
            },
            type_u.clone(),
        );
        let list = TypedTerm::adt_name(res.header.index, list_ty);
        let list_t = |i| {
            TypedTerm::make_application(
                list.clone(),
                TypedTerm::bound_variable(i, id_t, type_u.clone()),
                type_u.clone(),
            )
        };

        let type_constructor = env.resolve_path(id_list.borrow(), &args_u).unwrap();

        assert_eq!(type_constructor, list);

        let nil_const = env
            .resolve_path(id_list.clone().append(nil.name).borrow(), &args_u)
            .unwrap();

        assert_eq!(
            nil_const,
            TypedTerm::adt_constructor(
                res.header.index,
                0,
                TypedTerm::make_pi_type(
                    TypedBinder {
                        name: Some(id_t),
                        ty: type_u.clone()
                    },
                    list_t(0)
                )
            )
        );

        let succ_const = env
            .resolve_path(id_list.clone().append(cons.name).borrow(), &args_u)
            .unwrap();

        assert_eq!(
            succ_const,
            TypedTerm::adt_constructor(
                res.header.index,
                1,
                TypedTerm::make_pi_type(
                    TypedBinder {
                        name: Some(id_t),
                        ty: type_u.clone()
                    },
                    TypedTerm::make_pi_type(
                        TypedBinder {
                            name: None,
                            ty: TypedTerm::bound_variable(0, id_t, type_u.clone())
                        },
                        TypedTerm::make_pi_type(
                            TypedBinder {
                                name: None,
                                ty: list_t(1)
                            },
                            list_t(2)
                        )
                    )
                )
            )
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

        let level_u = Level::parameter(0, *id_u);
        let sort_u = TypedTerm::sort_literal(level_u.clone());
        let type_t = TypedTerm::bound_variable(1, id_t, sort_u.clone());
        let prop = TypedTerm::sort_literal(Level::zero());

        // Check the header
        assert_eq!(res.header.level_params, LevelParameters(vec![*id_u]));
        assert_eq!(
            res.header.parameters,
            vec![
                TypedBinder {
                    name: Some(id_t),
                    ty: sort_u.clone()
                },
                TypedBinder {
                    name: Some(id_x),
                    ty: TypedTerm::bound_variable(0, id_t, sort_u.clone()),
                }
            ]
        );
        assert_eq!(
            res.header.indices,
            vec![TypedBinder {
                name: None,
                ty: type_t.clone()
            }]
        );
        assert_eq!(res.header.sort, Level::zero());
        let t_to_prop = |t| {
            TypedTerm::make_pi_type(
                TypedBinder {
                    name: None,
                    ty: TypedTerm::bound_variable(t, id_t, sort_u.clone()),
                },
                prop.clone(),
            )
        };
        assert_eq!(res.header.family, t_to_prop(1));
        assert_eq!(res.header.is_prop, true);
        assert_eq!(res.is_large_eliminating, true);

        // Check the constructor
        let [refl] = res.constructors.as_slice() else {
            panic!("Wrong number of constructors");
        };

        assert!(refl.params.is_empty());
        assert_eq!(
            refl.indices,
            vec![
                type_t.clone(),
                TypedTerm::bound_variable(0, id_x, type_t.clone()),
                TypedTerm::bound_variable(0, id_x, type_t.clone()),
            ]
        );

        // Check the generated constants
        let args_u = LevelArgs(vec![level_u.clone()]);
        let type_constructor = env.resolve_path(ast.name.borrow(), &args_u).unwrap();
        let x_to_t_to_prop = |t| {
            TypedTerm::make_pi_type(
                TypedBinder {
                    name: Some(id_x),
                    ty: TypedTerm::bound_variable(t, id_t, sort_u.clone()),
                },
                t_to_prop(t + 1).clone(),
            )
        };
        let t_to_x_to_t_to_prop = TypedTerm::make_pi_type(
            TypedBinder {
                name: Some(id_t),
                ty: sort_u.clone(),
            },
            x_to_t_to_prop(0).clone(),
        );
        assert_eq!(
            type_constructor,
            TypedTerm::adt_name(res.header.index, t_to_x_to_t_to_prop)
        );

        let refl_const = env
            .resolve_path(ast.name.clone().append(refl.name).borrow(), &args_u)
            .unwrap();

        let eq_t_x_x = TypedTerm::make_application(
            TypedTerm::make_application(
                TypedTerm::make_application(
                    type_constructor,
                    TypedTerm::bound_variable(1, id_t, sort_u.clone()),
                    x_to_t_to_prop(1),
                ),
                TypedTerm::bound_variable(0, id_x, type_t.clone()),
                t_to_prop(1),
            ),
            TypedTerm::bound_variable(0, id_x, type_t.clone()),
            prop,
        );

        let refl_const_expected = TypedTerm::adt_constructor(
            res.header.index,
            0,
            TypedTerm::make_pi_type(
                TypedBinder {
                    name: Some(id_t),
                    ty: sort_u.clone(),
                },
                TypedTerm::make_pi_type(
                    TypedBinder {
                        name: Some(id_x),
                        ty: TypedTerm::bound_variable(0, id_t, sort_u.clone()),
                    },
                    eq_t_x_x,
                ),
            ),
        );

        env.pretty_println_val(&refl_const.ty);
        env.pretty_println_val(&refl_const_expected.ty);

        assert_eq!(refl_const, refl_const_expected);

        // TODO: check the type of the recursor
    }

    #[test]
    fn test_invalid_adt_definitions() {
        assert_type_error!(
            "data False : Prop where
            
            data Ty : False where",
            TypeError::NotASortFamily(TypedTerm::adt_name(
                AdtIndex(0),
                TypedTerm::sort_literal(Level::zero())
            ))
        );

        assert_type_error!(
            "data Ty.{u} : Sort u where",
            TypeError::MayOrMayNotBeProp(Level::parameter(0, Identifier::dummy()))
        );

        assert_type_error!(
            "data Ty : Type where
               | c : Prop
            ",
            TypeError::IncorrectConstructorResultantType {
                name: Identifier::dummy_val(7),
                found: TypedTerm::sort_literal(Level::zero()),
                expected: AdtIndex(0),
            }
        );

        assert_type_error!(
            "data False : Prop where
            
            data Ty : Prop where
               | c : (Ty -> Prop) -> Ty",
            TypeError::InvalidLocationForAdtNameInConstructor(AdtIndex(1))
        );

        assert_type_error!(
            "data False : Prop where

            data Ty : Prop -> Prop where
               | c : Ty (Ty False)",
            TypeError::InvalidLocationForAdtNameInConstructor(AdtIndex(1))
        );

        assert_type_error!(
            "data False : Type where
            
            data Ty (T : Type) : Type where
               | constructor : Ty False",
            TypeError::MismatchedAdtParameter {
                found: TypedTerm::adt_name(
                    AdtIndex(0),
                    TypedTerm::sort_literal(Level::constant(1))
                ),
                expected: TypedTerm::bound_variable(
                    0,
                    Identifier::dummy_val(9),
                    TypedTerm::sort_literal(Level::constant(1))
                )
                .term
            }
        );

        assert_type_error!(
            "data Ty : Type where
               | c : Type -> Ty",
            TypeError::InvalidConstructorParameterLevel {
                ty: TypedTerm::sort_literal(Level::constant(1)),
                adt_level: Level::constant(1)
            }
        );
    }
}
