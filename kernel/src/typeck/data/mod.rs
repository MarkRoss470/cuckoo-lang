//! The [`Adt`] and related types

use crate::typeck::context::TypingContext;
use crate::typeck::error::TypeErrorKind;
use crate::typeck::level::{Level, LevelArgs};
use crate::typeck::term::{TypedBinder, TypedTerm, TypedTermKind};
use crate::typeck::{AdtIndex, PrettyPrintContext, TypeError, TypingEnvironment};
use common::{Identifier, PrettyPrint};
use parser::ast::item::LevelParameters;
use parser::ast::item::data::{DataConstructor, DataDefinition};
use parser::atoms::ident::{OwnedPath, Path};
use parser::error::Span;
use std::io::Write;

mod recursor;

/// The header of an [`Adt`], i.e. everything except the constructors
#[derive(Debug)]
pub struct AdtHeader {
    /// The source span of the header of the ADT
    pub span: Span,
    /// The index into [`adts`] of this ADT
    ///
    /// [`adts`]: TypingEnvironment::adts
    pub index: AdtIndex,
    /// The ADT's name
    pub name: OwnedPath,
    /// The ADT's level parameters
    pub level_params: LevelParameters,
    /// The ADT's parameters (any binder before the colon)
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

/// An algebraic data type, declared with the `data` keyword
#[derive(Debug)]
pub struct Adt {
    /// The source span of the whole ADT declaration
    pub span: Span,
    /// The ADT's header
    pub header: AdtHeader,
    /// The ADT's constructors
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
    /// Gets the ADT's type constructor, i.e. the term which the ADT's name refers to
    fn type_constructor(&self) -> TypedTerm {
        TypedTerm::adt_name(
            self.index,
            TypedTerm::make_telescope(
                self.parameters.clone(),
                self.family.clone(),
                self.span.clone(),
            ),
            LevelArgs::from_level_parameters(&self.level_params),
            self.span.clone(),
        )
    }

    /// Gets a term referring to one of the ADT's constructors
    ///
    /// # Parameters
    /// * `index`: The index of the constructor
    /// * `type_without_adt_params`: The type of the constructor as written in the declaration
    /// * `span`: The source span of the constructor
    fn constructor(
        &self,
        index: usize,
        type_without_adt_params: TypedTerm,
        span: Span,
    ) -> TypedTerm {
        TypedTerm::adt_constructor(
            self.index,
            index,
            TypedTerm::make_telescope(
                self.parameters.clone(),
                type_without_adt_params,
                span.clone(),
            ),
            LevelArgs::from_level_parameters(&self.level_params),
            span,
        )
    }
}

impl Adt {
    /// Calculates and stores whether the ADT is large eliminating
    fn calculate_large_eliminating(&mut self) {
        self.is_large_eliminating = !self.header.is_prop || self.is_syntactically_subsingleton();
    }

    /// Calculates whether the ADT is syntactically subsingleton.
    ///
    /// An ADT is syntactically subsingleton if the structure of the definition guarantees that
    /// it has at most one instance for any given set of indices. This is the case when:
    /// * It has at most one constructor
    /// * Every parameter to the constructor is either a type in `Prop`, or is mentioned as one
    ///   of the constructor output's indices
    ///
    /// Normally, propositions can only be soundly eliminated to other propositions, because proof
    /// irrelevance means that all terms of a type in `Prop` are definitionally equal, but
    /// different proofs may eliminate to different values, allowing for proving false statements
    /// such as `0 = 1` if such propositions could eliminate to e.g. `Nat`.
    ///
    /// However, propositions which are syntactically subsingleton are guaranteed to never have more
    /// than one proof, so they can eliminate to types in higher universes without introducing
    /// inconsistency.
    fn is_syntactically_subsingleton(&self) -> bool {
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
        // or is one of the constructor's indices
        for (i, parameter) in constructor.params.iter().rev().enumerate() {
            if let AdtConstructorParamKind::NonInductive = &parameter.kind {
                let is_prop = parameter.ty.check_is_ty().unwrap().def_eq(&Level::zero());
                let is_referenced = constructor.indices.iter().any(|t| {
                    t.term()
                        .equiv(&TypedTermKind::bound_variable(i, parameter.name), false)
                });

                if !(is_prop || is_referenced) {
                    return false;
                }
            }
        }

        true
    }
}

/// A constructor of an [`Adt`]
#[derive(Debug)]
pub struct AdtConstructor {
    /// The source span of the constructor
    pub span: Span,
    /// The name of the constructor
    pub name: Identifier,
    /// The term referring to this constructor
    pub constant: TypedTerm,
    /// The whole type of the constructor, not including the ADT parameters
    pub type_without_adt_params: TypedTerm,
    /// The inputs to the constructor
    pub params: Vec<AdtConstructorParam>,
    /// The indices of the ADT instance produced by the constructor
    pub indices: Vec<TypedTerm>,
}

/// A parameter to an [`AdtConstructor`]
#[derive(Debug)]
pub struct AdtConstructorParam {
    /// The source span of the parameter
    pub span: Span,
    /// The name of the parameter
    pub name: Option<Identifier>,
    /// The type of the parameter
    pub ty: TypedTerm,
    /// Whether the parameter is inductive or not
    pub kind: AdtConstructorParamKind,
}

/// Whether a constructor parameter is inductive or not
#[derive(Debug)]
pub enum AdtConstructorParamKind {
    /// The parameter is inductive, meaning it is a function returning an instance
    /// of the [`Adt`] being defined.
    Inductive {
        /// The parameters to the function type
        parameters: Vec<TypedBinder>,
        /// The parameters and indices of the [`Adt`] which is the return type of the function
        args: Vec<TypedTerm>,
    },
    /// The parameter is non-inductive, meaning it does not mention the [`Adt`] being defined
    NonInductive,
}

impl AdtConstructor {
    /// Returns an iterator over only the inductive parameters of the constructor.
    /// Each item of the iterator is the parameter's index, [`parameters`], and [`args`].
    ///
    /// [`parameters`]: AdtConstructorParamKind::Inductive::parameters
    /// [`args`]: AdtConstructorParamKind::Inductive::args
    pub fn inductive_params(&self) -> impl Iterator<Item = (usize, &[TypedBinder], &[TypedTerm])> {
        self.params
            .iter()
            .enumerate()
            .filter_map(|(i, param)| match &param.kind {
                AdtConstructorParamKind::Inductive { parameters, args } => {
                    Some((i, parameters.as_slice(), args.as_slice()))
                }
                AdtConstructorParamKind::NonInductive => None,
            })
    }
}

impl<'a> TypingEnvironment {
    /// Resolves an ADT definition, adding it to [`adts`].
    ///
    /// [`adts`]: TypingEnvironment::adts
    pub(super) fn resolve_adt(&mut self, ast: &'a DataDefinition) -> Result<(), TypeError> {
        // Set the level parameters for this item
        self.set_level_params(ast.level_params.clone())?;

        // Resolve the header
        let adt_index = AdtIndex(self.adts.len());
        let header = self.resolve_adt_header(ast, adt_index)?;

        // Add a stub ADT to `self.ads` so that if this ADT shows up in any errors while resolving the constructors,
        // it can be printed properly
        self.adts.push(Adt {
            span: ast.span.clone(),
            header,
            constructors: vec![],
            is_large_eliminating: false,
        });
        let header = &self.adts.last().unwrap().header;

        // Resolve the constructors
        let constructors = self.resolve_adt_constructors(ast, header)?;
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

        // If configured, check that the recursor type is a valid term
        if self.config.check_terms {
            self.check_term(&recursor.get_type());
        }

        // Create the recursor constant
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

    /// Resolve an [`AdtHeader`]
    fn resolve_adt_header(
        &mut self,
        ast: &'a DataDefinition,
        index: AdtIndex,
    ) -> Result<AdtHeader, TypeError> {
        let root = TypingContext::Root(self);

        // Resolve the ADT's parameters
        let mut parameters = Vec::new();
        for param in &ast.parameters {
            // Check that the binder has exactly one name
            let [binder_name] = param.names.as_slice() else {
                return Err(TypeError::unsupported(
                    param.span.clone(),
                    "Multiple names in a binder",
                ));
            };

            // Resolve the binder's type in a context with all the previous parameters
            let context = root.with_binders(&parameters);
            let ty = context.resolve_term(&param.ty)?;
            ty.check_is_ty()?;

            // Add the new parameter
            parameters.push(TypedBinder {
                span: param.span.clone(),
                name: *binder_name,
                ty,
            })
        }

        // Resolve the family in a context with all the parameters
        let context = root.with_binders(&parameters);
        let family = context.resolve_term(&ast.family)?;

        // Check that the ADT's family is a type
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
            span: ast.span.start_point().union(&ast.family.span),
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

    /// Resolves an [`Adt`]'s constructors
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

    /// Resolves a single [`AdtConstructor`]
    ///
    /// # Parameters
    /// * `constructor`: The AST of the constructor to resolve
    /// * `index`: The index of the constructor in the [`Adt`]
    /// * `ty`: The type of the constructor as written in the ADT declaration
    ///   (this therefore does not include the ADT's parameters, which will be included in the
    ///   type of the constructor constant)
    /// * `header`: The ADT's header
    fn resolve_adt_constructor(
        &self,
        constructor: &DataConstructor,
        index: usize,
        ty: &TypedTerm,
        header: &AdtHeader,
    ) -> Result<AdtConstructor, TypeError> {
        // Check that the constructor's type is actually a type, and decompose it as a telescope
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

        // Resolve the constructor's parameters
        let mut processed_params = Vec::new();
        for param in parameters {
            processed_params.push(self.resolve_adt_constructor_param(header.index, param)?);
        }

        Ok(AdtConstructor {
            span: constructor.span.clone(),
            name: constructor.name,
            constant: header.constructor(index, ty.clone(), constructor.span.clone()),
            type_without_adt_params: ty.clone(),
            params: processed_params,
            indices: arguments,
        })
    }

    /// Resolves an [`AdtConstructorParam`]
    fn resolve_adt_constructor_param(
        &self,
        adt_index: AdtIndex,
        param: TypedBinder,
    ) -> Result<AdtConstructorParam, TypeError> {
        // Decompose the parameter's type as a function telescope resulting in an application stack
        let (parameters, output) = param.ty.clone().decompose_telescope();
        let (f, args) = output.decompose_application_stack();

        // If f is the ADT being constructed, then this is an inductive parameter
        let param_kind = if let Some((id, _)) = f.is_adt_name()
            && id == adt_index
        {
            // The parameters and indices of the parameter may not reference the ADT being defined
            for binder in &parameters {
                binder.ty.forbid_references_to_adt(adt_index)?;
            }
            for arg in &args {
                arg.forbid_references_to_adt(adt_index)?;
            }

            AdtConstructorParamKind::Inductive { parameters, args }
        } else {
            param.ty.forbid_references_to_adt(adt_index)?;

            AdtConstructorParamKind::NonInductive
        };

        Ok(AdtConstructorParam {
            span: param.span,
            name: param.name,
            ty: param.ty,
            kind: param_kind,
        })
    }

    /// Resolves the output of an [`AdtConstructor`]
    ///
    /// # Parameters
    /// * `ty`: The type of the constructor's output
    /// * `name`: The name of the constructor
    /// * `constructor_params`: The parameters of the constructor
    /// * `header`: The header of the [`Adt`] the constructor is for
    fn resolve_adt_constructor_output(
        &self,
        ty: TypedTerm,
        name: Identifier,
        constructor_params: &[TypedBinder],
        header: &AdtHeader,
    ) -> Result<Vec<TypedTerm>, TypeError> {
        // Decompose the output of the telescope as a series of applications.
        // The underlying function should be the name of the ADT being constructed
        let (f, arguments) = ty.decompose_application_stack();

        // Check that the underlying function is the correct ADT name
        match f.is_adt_name() {
            Some((id, _)) if id == header.index => {}
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
            let expected = TypedTermKind::bound_variable(
                constructor_params.len() + header.parameters.len() - i - 1,
                param.name,
            );

            if !arguments[i].term().equiv(&expected, false) {
                return Err(TypeError {
                    span: arguments[i].span(),
                    kind: TypeErrorKind::MismatchedAdtParameter {
                        found: arguments[i].clone(),
                        expected,
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

    /// Checks that the level of the parameter `param` is less than the level of the [`Adt`]
    ///
    /// # Parameters
    /// * `param`: The parameter to check
    /// * `adt_level`: The level of the ADT
    fn check_adt_parameter_levels(
        &self,
        param: &TypedBinder,
        adt_level: &Level,
    ) -> Result<(), TypeError> {
        if !adt_level.is_geq(&param.level()) {
            Err(TypeError {
                span: param.span.clone(),
                kind: TypeErrorKind::InvalidConstructorParameterLevel {
                    ty: param.ty.clone(),
                    adt_level: adt_level.clone(),
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
