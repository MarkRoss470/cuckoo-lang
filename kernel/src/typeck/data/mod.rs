use crate::diagnostic::KernelError::Type;
use crate::typeck::error::TypeErrorKind;
use crate::typeck::level::{Level, LevelArgs};
use crate::typeck::term::{TypedBinder, TypedTerm};
use crate::typeck::{AdtIndex, PrettyPrintContext, TypeError, TypingContext, TypingEnvironment};
use common::{Identifier, PrettyPrint};
use parser::ast::item::LevelParameters;
use parser::ast::item::data::{DataConstructor, DataDefinition};
use parser::atoms::ident::{OwnedPath, Path};
use parser::error::Span;
use std::io::Write;

mod recursor;
#[cfg(test)]
mod tests;

#[derive(Debug)]
pub struct AdtHeader {
    pub span: Span,
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
    pub sort: Level,
    /// Whether the ADT is a proposition
    pub is_prop: bool,
}

#[derive(Debug)]
pub struct Adt {
    pub span: Span,
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
        TypedTerm::adt_name(
            self.index,
            TypedTerm::make_telescope(self.parameters.clone(), self.family.clone(), self.span),
            LevelArgs::from_level_parameters(&self.level_params),
            self.span,
        )
    }

    fn constructor(
        &self,
        index: usize,
        type_without_adt_params: TypedTerm,
        span: Span,
    ) -> TypedTerm {
        TypedTerm::adt_constructor(
            self.index,
            index,
            TypedTerm::make_telescope(self.parameters.clone(), type_without_adt_params, span),
            LevelArgs::from_level_parameters(&self.level_params),
            span,
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
                let is_prop = ty.level().def_eq(&Level::zero());
                let is_referenced = constructor
                    .indices
                    .iter()
                    .any(|t| t.term().references_bound_variable(i));

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
    pub span: Span,
    pub name: Identifier,
    /// The term referring to this constructor
    pub constant: TypedTerm,
    /// The whole type of the constructor, not including the ADT parameters
    pub type_without_adt_params: TypedTerm,
    /// The inputs to the constructor
    pub params: Vec<AdtConstructorParam>,
    /// The [`indices`] of the ADT produced by the constructor
    ///
    /// [`indices`]: Adt::indices
    pub indices: Vec<TypedTerm>,
}

#[cfg_attr(any(test, debug_assertions), derive(PartialEq))]
#[derive(Debug)]
pub struct AdtConstructorParam {
    pub span: Span,
    pub name: Option<Identifier>,
    pub ty: TypedTerm,
    pub kind: AdtConstructorParamKind,
}

#[cfg_attr(any(test, debug_assertions), derive(PartialEq))]
#[derive(Debug)]
pub enum AdtConstructorParamKind {
    Inductive {
        parameters: Vec<TypedBinder>,
        indices: Vec<TypedTerm>,
    },
    NonInductive(TypedTerm),
}

impl AdtConstructor {
    pub fn inductive_params(&self) -> impl Iterator<Item = (usize, &[TypedBinder], &[TypedTerm])> {
        self.params
            .iter()
            .enumerate()
            .filter_map(|(i, param)| match &param.kind {
                AdtConstructorParamKind::Inductive {
                    parameters,
                    indices,
                } => Some((i, parameters.as_slice(), indices.as_slice())),
                AdtConstructorParamKind::NonInductive(_) => None,
            })
    }
}

impl<'a> TypingEnvironment {
    pub(super) fn resolve_adt(&mut self, ast: &'a DataDefinition) -> Result<(), TypeError> {
        // Set the level parameters for this item
        self.set_level_params(ast.level_params.clone())?;

        // Resolve the header
        let adt_index = AdtIndex(self.adts.len());
        let header = self.resolve_adt_header(ast, adt_index)?;

        // Add a stub ADT to `self.ads` so that if this ADT shows up in any errors while resolving the constructors,
        // it can be printed properly
        self.adts.push(Adt {
            span: ast.span,
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
            adt.span.start_point(),
        )?;

        // Create the constructor constants
        let adt_namespace = self
            .root
            .resolve_namespace_mut(name, adt.span.start_point())?;
        for constructor in &adt.constructors {
            adt_namespace.insert(
                Path::from_id(&constructor.name),
                level_parameters.clone(),
                constructor.constant.clone(),
                constructor.span.start_point(),
            )?;
        }

        // Create the recursor
        let (recursor_level_params, recursor) = self.generate_recursor(self.adts.last().unwrap());

        #[cfg(debug_assertions)]
        self.check_term(recursor.get_type());

        let adt_namespace = self
            .root
            .resolve_namespace_mut(adt.header.name.borrow(), adt.span.start_point())?;
        adt_namespace.insert(
            Path::from_id(&Identifier::from_str(
                "rec",
                &mut self.interner.borrow_mut(),
            )),
            recursor_level_params,
            recursor,
            adt.span.start_point(),
        )?;

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
            let [binder_name] = param.names.as_slice() else {
                return Err(TypeError::unsupported(
                    param.span,
                    "Multiple names in a binder",
                ));
            };

            let context = root.with_binders(&parameters);
            let ty = context.resolve_term(&param.ty)?;
            parameters.push(TypedBinder {
                span: param.span,
                name: *binder_name,
                ty,
            })
        }
        let context = root.with_binders(&parameters);

        let family = context.resolve_term(&ast.family)?;

        let Ok(_) = family.check_is_ty() else {
            return Err(TypeError {
                span: family.span(),
                kind: TypeErrorKind::NotASortFamily(family),
            });
        };

        // Resolve the type's family as a telescope
        let (indices, out) = family.clone().decompose_telescope();
        // Check that the output of the telescope is a sort
        let Ok(sort) = out.term().check_is_sort() else {
            return Err(TypeError {
                span: out.span(),
                kind: TypeErrorKind::NotASortFamily(family),
            });
        };

        // Check that the ADT is either always in `Prop` or always not in `Prop`
        let is_prop = if sort.def_eq(&Level::zero()) {
            true
        } else if sort.is_geq(&Level::constant(1)) {
            false
        } else {
            return Err(TypeError {
                span: out.span(),
                kind: TypeErrorKind::MayOrMayNotBeProp(sort),
            });
        };

        Ok(AdtHeader {
            span: ast.span.start_point().union(ast.family.span),
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
            span: ast.span.start_point(),
            name: Some(ast.name.last()),
            ty: type_constructor.get_type(),
        };
        let root = TypingContext::Root(self);
        let context = root.with_binder(&adt_name_binder);
        let context = context.with_binders(&header.parameters);

        let mut constructors = Vec::new();

        for (i, constructor) in ast.constructors.iter().enumerate() {
            let ty = context
                .resolve_term(&constructor.telescope)?
                // The binder which refers to the ADT name comes after all the parameter names
                .replace_binder(header.parameters.len(), &type_constructor);

            let constructor = self.resolve_adt_constructor(constructor, i, &ty, header)?;

            constructors.push(constructor);
        }

        Ok(constructors)
    }

    fn resolve_adt_constructor(
        &self,
        constructor: &DataConstructor,
        index: usize,
        ty: &TypedTerm,
        header: &AdtHeader,
    ) -> Result<AdtConstructor, TypeError> {
        // Check that the constructor is actually a type, and decompose it as a telescope
        ty.check_is_ty()?;
        let (parameters, output) = ty.clone().decompose_telescope();

        // Check that the output type is legal
        let arguments =
            self.resolve_adt_constructor_output(output, constructor.name, &parameters, header)?;

        // Check that the levels of parameters are legal.
        // This doesn't matter for Prop types as parameters for those can be any level.
        if !header.is_prop {
            for param in &parameters {
                self.check_adt_parameter_levels(param, &header.sort)?;
            }
        }

        let mut processed_params = Vec::new();
        for param in parameters {
            processed_params.push(self.resolve_adt_constructor_param(header.index, param)?);
        }

        Ok(AdtConstructor {
            span: constructor.span,
            name: constructor.name,
            constant: header.constructor(index, ty.clone(), constructor.span),
            type_without_adt_params: ty.clone(),
            params: processed_params,
            indices: arguments,
        })
    }

    fn resolve_adt_constructor_param(
        &self,
        adt_index: AdtIndex,
        param: TypedBinder,
    ) -> Result<AdtConstructorParam, TypeError> {
        let (parameters, output) = param.ty.clone().decompose_telescope();
        let (f, args) = output.decompose_application_stack();

        // If f is the ADT being constructed, then this is an inductive parameter
        let param_kind = if let Some((id, _)) = f.is_adt_name()
            && id == adt_index
        {
            for binder in &parameters {
                binder.ty.forbid_references_to_adt(adt_index)?;
            }
            for arg in &args {
                arg.forbid_references_to_adt(adt_index)?;
            }

            AdtConstructorParamKind::Inductive {
                parameters,
                indices: args,
            }
        } else {
            param.ty.forbid_references_to_adt(adt_index)?;

            AdtConstructorParamKind::NonInductive(param.ty.clone())
        };

        Ok(AdtConstructorParam {
            span: param.span,
            name: param.name,
            ty: param.ty,
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
        match f.is_adt_name() {
            Some((id, _)) if id == header.index => (),
            _ => {
                return Err(TypeError {
                    span: f.span(),
                    kind: TypeErrorKind::IncorrectConstructorResultantType {
                        name,
                        found: f,
                        expected: header.index,
                    },
                });
            }
        }

        // Check that the parameters are exactly the same as in the ADT header
        for (i, param) in header.parameters.iter().enumerate() {
            let expected = TypedTerm::bound_variable(
                constructor_params.len() + header.parameters.len() - i - 1,
                param.name,
                param
                    .ty
                    .clone_incrementing(0, constructor_params.len() + header.parameters.len() - i),
                param.span,
            );

            if !self.def_eq(arguments[i].clone(), expected.clone()) {
                return Err(TypeError {
                    span: arguments[i].span(),
                    kind: TypeErrorKind::MismatchedAdtParameter {
                        found: arguments[i].clone(),
                        expected: expected.term(),
                    },
                });
            }
        }

        // Check that the arguments do not include references to the current ADT
        for argument in &arguments {
            argument.forbid_references_to_adt(header.index)?;
        }

        Ok(arguments)
    }

    fn check_adt_parameter_levels(
        &self,
        param: &TypedBinder,
        adt_sort: &Level,
    ) -> Result<(), TypeError> {
        if !adt_sort.is_geq(&param.level()) {
            Err(TypeError {
                span: param.span,
                kind: TypeErrorKind::InvalidConstructorParameterLevel {
                    ty: param.ty.clone(),
                    adt_level: adt_sort.clone(),
                },
            })
        } else {
            Ok(())
        }
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
        self.name.pretty_print(out, &context.interner())?;
        self.level_params.pretty_print(out, &context.interner())?;

        for parameter in &self.parameters {
            write!(out, " ")?;
            parameter.pretty_print(out, context)?;
        }

        write!(out, " : ")?;

        self.family.pretty_print(out, context)?;

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
        self.name.pretty_print(out, &context.interner())?;
        write!(out, " : ")?;
        self.type_without_adt_params
            .term()
            .pretty_print(out, context)?;
        writeln!(out)
    }
}
