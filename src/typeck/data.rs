use crate::parser::ast::item::LevelParameters;
use crate::parser::ast::item::data::DataDefinition;
use crate::parser::ast::term::LevelExpr;
use crate::parser::atoms::ident::{Identifier, OwnedPath, Path};
use crate::typeck::level::Level;
use crate::typeck::term::{TypedBinder, TypedTerm, TypedTermKind};
use crate::typeck::{AdtIndex, TypeError, TypingContext, TypingEnvironment};
use std::rc::Rc;

#[derive(Debug)]
pub struct Adt {
    pub name: OwnedPath,
    pub level_params: LevelParameters,
    pub parameters: Vec<TypedBinder>,
    pub indices: Vec<TypedBinder>,
    pub sort: Rc<Level>,
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

impl<'a> TypingEnvironment<'a> {
    pub(super) fn resolve_data_definition(
        &mut self,
        ast: &'a DataDefinition,
    ) -> Result<(), TypeError> {
        // Set the level parameters for this item
        self.set_level_params(&ast.level_params)?;

        // TODO: resolve parameters

        let family = TypingContext::Root(self).resolve_term(&ast.family)?;

        let Ok(family_level) = family.check_is_ty() else {
            return Err(TypeError::NotASortFamily(family));
        };

        // Resolve the type's family as a telescope
        let (indices, out) = family.clone().into_telescope();
        // Check that the output of the telescope is a sort
        let Ok(sort) = out.term.check_is_sort() else {
            return Err(TypeError::NotASortFamily(family));
        };

        // TODO: check that the ADT's level is at least as large as the levels of all parameters,
        // and larger than the levels of all indices

        let adt_index = AdtIndex(self.adts.len());

        // Add a stub ADT to `self.ads` so that if this ADT shows up in any errors while resolving the constructors,
        // it can be printed properly
        self.adts.push(Adt {
            name: ast.name.clone(),
            level_params: ast.level_params.clone(),
            parameters: vec![], // TODO
            indices,
            sort,
            constructors: vec![],
        });

        // The term that the ADT name should resolve to
        let adt_name_value = TypedTerm {
            level: family_level,
            ty: family.term,
            term: TypedTermKind::AdtName(adt_index),
        };
        let constructors = self.resolve_adt_constructors(&ast, adt_index, &adt_name_value)?;

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
                    level: Rc::new(Level::Zero),
                    ty: constructor.ty.clone(),
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

    fn resolve_adt_constructors(
        &mut self,
        ast: &&DataDefinition,
        adt_index: AdtIndex,
        adt_name_value: &TypedTerm,
    ) -> Result<Vec<AdtConstructor>, TypeError> {
        // Set up a TypingContext to resolve the constructor types in
        let binder = TypedBinder {
            name: Some(ast.name.last()),
            ty: TypedTerm {
                level: adt_name_value.level.succ(),
                ty: TypedTermKind::SortLiteral(adt_name_value.level.clone()),
                term: adt_name_value.ty.clone(),
            },
        };
        let context = TypingContext::Binder {
            binder: &binder,
            parent: &TypingContext::Root(self),
        };

        let mut constructors = Vec::new();

        for constructor in &ast.constructors {
            let ty = context
                .resolve_term(&constructor.telescope)?
                .replace_binder(0, adt_name_value);

            let constructor = self.resolve_adt_constructor(constructor.name, &ty, adt_index)?;

            constructors.push(constructor);
        }

        Ok(constructors)
    }

    fn resolve_adt_constructor(
        &self,
        name: Identifier,
        ty: &TypedTerm,
        adt_index: AdtIndex,
    ) -> Result<AdtConstructor, TypeError> {
        // Check that the constructor is actually a type, and decompose it as a telescope
        ty.check_is_ty()?;
        let (params, output) = ty.clone().into_telescope();

        let mut processed_params = Vec::new();
        for param in params {
            processed_params.push(self.resolve_adt_constructor_param(name, adt_index, param)?);
        }

        let arguments = self.resolve_adt_constructor_output(output, name, adt_index)?;

        Ok(AdtConstructor {
            name,
            ty: ty.term.clone(),
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
        let (parameters, output) = param.ty.clone().into_telescope();
        let (f, args) = output.into_application_stack();

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
            name: Some(name),
            kind: param_kind,
        })
    }

    fn resolve_adt_constructor_output(
        &self,
        output: TypedTerm,
        name: Identifier,
        adt_index: AdtIndex,
    ) -> Result<Vec<TypedTerm>, TypeError> {
        // Decompose the output of the telescope as a series of applications.
        // The underlying function should be the name of the ADT being constructed
        let (f, arguments) = output.into_application_stack();

        // Check that the underlying function is the correct ADT name
        match f.term {
            TypedTermKind::AdtName(id) if id == adt_index => (),

            _ => {
                return Err(TypeError::IncorrectConstructorResultantType {
                    name,
                    found: f,
                    expected: adt_index,
                });
            }
        }

        // Check that the arguments do not include references to the current ADT
        for argument in &arguments {
            argument.term.forbid_references_to_adt(adt_index)?;
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
