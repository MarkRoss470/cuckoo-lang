use crate::typeck::TypingEnvironment;
use crate::typeck::data::{Adt, AdtConstructor, AdtConstructorParamKind};
use crate::typeck::level::{Level, LevelArgs};
use crate::typeck::term::{TypedBinder, TypedTerm, TypedTermKind};
use std::iter;
use common::{Identifier, Interner};
use parser::ast::item::LevelParameters;

impl<'a> TypingEnvironment {
    /// Generates the recursor constant of an ADT. This constant is of the following type:
    ///
    /// `<ADT params> -> <motive type> -> <constructor induction rules> -> <indices> -> <ADT value> -> <motive output>` where:
    /// * `<ADT params>` are the ADT's parameters as specified in the ADT's header
    /// * The motive type is a type parameterized by the ADT's indices and a particular value of the
    ///     ADT with those indices. For [large eliminating] types, the output of this motive may live
    ///     in any universe and a new universe parameter is created on top of the ADT's ones for this,
    ///     while for types which are not large eliminating, the output of the motive must be in `Prop`.
    ///  * There is one constructor induction rule per constructor of the ADT. This is a function type
    ///     with the constructor's parameters as input as well as an input of the motive type for any
    ///     inductive parameters, and outputs an instance of the motive type for the constructor.
    ///
    /// [large eliminating]: Adt::is_large_eliminating
    ///
    /// The recursor allows for defining functions on an ADT by structural induction, with the
    /// motive giving the return type for any instance of the ADT, and the induction rules determining
    /// how to build up the motive for larger ADT instances given smaller ones. It also encapsulates
    /// the substitution principle of the `Eq` type, as it allows to construct a value of type
    /// `A y` given `A x` and `Eq T x y`.
    ///
    /// # Examples
    ///
    /// The type of the recursor of the `Nat` type is (up to variable renaming):
    /// ```
    ///     -- Nat has no parameters, so there is nothing before the motive
    ///     -- Motive
    /// (motive : Nat -> Sort m)
    ///     -- Induction rule for zero
    /// -> (zero : motive zero)
    ///     -- Induction rule for succ
    /// -> (succ : (x : Nat) -> motive x -> motive (succ x))
    ///     -- Nat has no indices, so there is nothing between the constructors and the ADT value
    ///     -- ADT value
    /// -> (x : Nat)
    ///     -- Motive output
    /// -> motive x
    /// ```
    ///
    /// The type of the recursor of the `List` type is:
    /// ```
    ///     -- Parameters
    /// (T : Type u)
    ///     -- Motive
    /// -> (motive : List T -> Sort m)
    ///     -- Induction rule for nil
    /// -> (nil : motive nil)
    ///     -- Induction rule for cons
    /// -> (cons : (x : T) -> (xs : List T) -> motive xs -> motive (cons T x xs))
    ///     -- List has no indices, so there is nothing between the constructors and the ADT value
    ///     -- ADT value
    /// -> (l : List T)
    ///     -- Motive output
    /// -> motive l
    /// ```
    ///
    /// The type of the recursor of the `Eq` type is:
    /// ```
    ///     -- Parameters
    /// (T : Sort u)
    /// -> (x : T)
    ///     -- Motive
    /// -> (motive : (y : T) -> Eq T x y -> Sort m)
    ///     -- Induction rule for refl
    /// -> (refl : motive x)
    ///     -- Indices
    /// -> (y : T)
    ///     -- ADT value
    /// -> (e : Eq T x y)
    ///     -- Motive output
    /// -> motive y e
    /// ```
    ///
    /// For an example with more complex induction principles, the accessibility relation `Acc` defined as:
    /// ```
    /// data Acc.{u} (T : Sort u) (R : T -> T -> Prop) : T -> Prop where
    ///   | acc : (x : T) -> ((y : T) -> R y x -> Acc T R y) -> Acc T R x
    /// ```
    ///
    /// has a recursor of type:
    /// ```
    /// (T : Sort u)
    /// -> (R : T -> T -> Prop)
    /// -> (motive : (x : T) -> Acc T R x -> Sort m)
    /// -> (acc :
    ///     -- Constructor parameters
    ///     (x : T)
    ///     -> (h : (y : T) -> (R y x) -> Acc T R y)
    ///     -- Induction principle for h
    ///     -> ((y : T) -> (hy : R y x) -> motive y (h y hy))
    ///     -- Output of induction principle for acc
    ///     -> motive x (acc T R x h)
    /// )
    /// -> (x : T)
    /// -> (a : Acc T R x)
    /// -> motive x a
    /// ```
    pub(super) fn generate_recursor(&self, adt: &Adt) -> (LevelParameters, TypedTerm) {
        let (level_params, motive_output_sort) =
            calculate_levels(adt, &mut self.interner.borrow_mut());

        // The parameters to the recursor
        let mut recursor_params = adt.header.parameters.clone();

        // Add the motive parameter
        let motive_ty = calculate_motive_type(adt, motive_output_sort);
        let motive_id = Identifier::from_str("motive", &mut self.interner.borrow_mut());
        recursor_params.push(TypedBinder {
            name: Some(motive_id),
            ty: motive_ty.clone(),
        });

        // Closure to generate `motive <indices> <val>`
        let motive = |offset, indices: Vec<TypedTerm>, val: TypedTerm| {
            make_motive(adt, motive_id, &motive_ty, offset, indices, val)
        };

        // Generate constructor induction rules
        generate_induction_rules(adt, &mut recursor_params, motive);

        // Add parameters for each of the ADT's indices
        for (i, index) in adt.header.indices.iter().enumerate() {
            recursor_params.push(TypedBinder {
                name: index.name,
                ty: index.ty.clone_incrementing(i, adt.constructors.len() + 1),
            })
        }

        // Add parameter for the value being recursed on
        let value_param_type = calculate_value_parameter_type(adt, recursor_params.len());
        recursor_params.push(TypedBinder {
            name: None,
            ty: value_param_type.clone(),
        });

        let output_type = calculate_output_type(adt, motive, value_param_type);

        // Generate final constant
        let recursor = TypedTerm::adt_recursor(
            adt.header.index,
            TypedTerm::make_telescope(recursor_params, output_type),
            LevelArgs::from_level_parameters(&level_params),
        );

        (level_params, recursor)
    }
}

/// Calculates the level parameters for the recursor of an ADT and the level of the motive
/// return type, based on whether the ADT is large eliminating. If the ADT is not large
/// eliminating, then the level parameters for the recursor are the same as those for the ADT,
/// and the motive return type is `Prop`. If the ADT is large eliminating, then an extra level
/// parameter is added for the motive.
fn calculate_levels(adt: &Adt, interner: &mut Interner) -> (LevelParameters, Level) {
    // If the ADT is large eliminating, add a level parameter for the level of the motive.
    // Otherwise, just copy the level parameters of the ADT, and the motive must be a Prop.
    let (level_params, motive_output_sort) = if adt.is_large_eliminating {
        let mut level_params = adt.header.level_params.clone();
        let id = adt.header.level_params.unused_ident_from("m", interner);
        level_params.0.push(id);
        let motive_ty = Level::parameter(level_params.count() - 1, id);

        (level_params, motive_ty)
    } else {
        (adt.header.level_params.clone(), Level::zero())
    };
    (level_params, motive_output_sort)
}

/// Calculates the type of the motive in the recursor of an ADT. The motive is of the form
/// `<indices> -> <value> -> Sort <motive output sort>>` where `<indices>` are the ADT's indices
/// and `<value>` is a value of the ADT with those indices.
fn calculate_motive_type(adt: &Adt, motive_output_sort: Level) -> TypedTerm {
    let mut motive_params = adt.header.indices.clone();

    motive_params.push(TypedBinder {
        name: None,
        ty: TypedTerm::make_application_stack(
            adt.header.type_constructor(), // TODO: don't recompute this
            adt.header
                .parameters
                .iter()
                .chain(adt.header.indices.iter())
                .enumerate()
                .map(|(i, binder)| {
                    TypedTermKind::bound_variable(
                        adt.header.parameters.len() + adt.header.indices.len() - i - 1,
                        binder.name,
                    )
                }),
        ),
    });

    TypedTerm::make_telescope(motive_params, TypedTerm::sort_literal(motive_output_sort))
}

/// Makes a term of the form `motive <indices> <val>`
///
/// # Parameters
/// * `adt`: The ADT whose recursor is being computed
/// * `motive_id`: The identifier `motive`
/// * `motive_ty`: The type of the motive for this ADT
/// * `motive_offset`: The number of binders between the motive parameter and where this term will be used
/// * `indices`: The indices to the motive application
/// * `val`: The ADT parameter to the motive application
fn make_motive(
    adt: &Adt,
    motive_id: Identifier,
    motive_ty: &TypedTerm,
    motive_offset: usize,
    indices: Vec<TypedTerm>,
    val: TypedTerm,
) -> TypedTerm {
    debug_assert!(matches!(
        val.get_type().decompose_application_stack().0.is_adt_name(),
        Some((id, _)) if id == adt.header.index
    ));
    debug_assert_eq!(
        val.get_type().decompose_application_stack().1.len(),
        adt.header.indices.len() + adt.header.parameters.len(),
    );
    debug_assert_eq!(indices.len(), adt.header.indices.len());

    TypedTerm::make_application_stack(
        TypedTerm::bound_variable(
            motive_offset,
            Some(motive_id),
            motive_ty.clone_incrementing(0, motive_offset + 1),
        ),
        indices
            .into_iter()
            .chain(iter::once(val))
            .map(|index| index.term()),
    )
}

/// Calculates the type of the value parameter to the recursor
///
/// # Params
/// * `adt`: The ADT whose recursor is being computed
/// * `num_params`: The number of parameters to the recursor before the value parameter.
///     This is used to offset the indices of the ADT parameters.
fn calculate_value_parameter_type(adt: &Adt, num_params: usize) -> TypedTerm {
    TypedTerm::make_application_stack(
        adt.header.type_constructor(), // TODO: don't recompute this
        adt.header
            .parameters
            .iter()
            .enumerate()
            .map(|(i, param)| TypedTermKind::bound_variable(num_params - i - 1, param.name))
            .chain(adt.header.indices.iter().enumerate().map(|(i, index)| {
                TypedTermKind::bound_variable(adt.header.indices.len() - i - 1, index.name)
            })),
    )
}

/// Calculates the output type for the recursor of an ADT.
///
/// # Parameters
/// * `adt`: The ADT in question
/// * `motive(offset, indices, val)`: Gets a term referring to an application of the
///     `motive` parameter of the recursor's type.
///     `indices` are the indices to the ADT instance that this motive is for.
///     `val` is the ADT instance that this motive is for.
/// * `value_parameter_type`: The type of the recursor's value parameter
fn calculate_output_type(
    adt: &Adt,
    motive: impl Fn(usize, Vec<TypedTerm>, TypedTerm) -> TypedTerm,
    value_parameter_type: TypedTerm,
) -> TypedTerm {
    motive(
        adt.constructors.len() + adt.header.indices.len() + 1,
        adt.header
            .indices
            .iter()
            .enumerate()
            .map(|(i, index)| {
                TypedTerm::bound_variable(
                    adt.header.indices.len() - i, // No `-1` here because the motive term cancels it out
                    index.name,
                    index.ty.clone_incrementing(0, adt.header.indices.len() + 1),
                )
            })
            .collect(),
        TypedTerm::bound_variable(0, None, value_parameter_type),
    )
}

/// Generates the constructor induction rules, adding them to `params`.
///
/// # Parameters
/// * `adt`: The ADT whose recursor is being computed
/// * `params`: Where to add the new parameters
/// * `motive(offset, indices, val)` : Gets a term referring to an application of the
///     `motive` parameter of the recursor's type.
///     `offset` is the number of binders between the motive parameter and the use of the motive.
///     `indices` are the indices to the ADT instance that this motive is for.
///     `val` is the ADT instance that this motive is for.
fn generate_induction_rules(
    adt: &Adt,
    recursor_params: &mut Vec<TypedBinder>,
    motive: impl Fn(usize, Vec<TypedTerm>, TypedTerm) -> TypedTerm,
) {
    // Generate constructor induction rules
    for (i, constructor) in adt.constructors.iter().enumerate() {
        let induction_rule = calculate_constructor_induction_rule(
            adt.header.parameters.len(),
            |index, offset| {
                TypedTermKind::bound_variable(
                    recursor_params.len() - index - 1 + offset,
                    adt.header.parameters[index].name,
                )
            },
            constructor,
            |binders, val| val.clone_incrementing(binders, i + 1),
            |offset, indices, val| motive(offset + i, indices, val),
        );

        recursor_params.push(TypedBinder {
            name: Some(constructor.name),
            ty: induction_rule,
        });
    }
}

/// Calculates the part of a recursor's type corresponding to induction on a specific constructor.
///
/// The format of this type is `<constructor params> -> <motives of inductive params> -> motive <indices>`
///
/// # Parameters
/// * `adt_num_params` : The number of parameters which that ADT has
/// * `get_adt_param(index, offset)` : Gets a term referencing one of the ADT's parameters.
///     `offset` is the number of binders between the root of the expression returned by
///     this function and the use of the ADT parameter.
/// * `constructor` : The constructor whose induction rule is being generated
/// * `reindex(binders, term)` : Clones a term while re-indexing binders referring to ADT parameters.
///     `binders` is the number of binders between the source term and the root of the constructor's type.
/// * `motive(offset, indices, val)` : Gets a term referring to an application of the
///     `motive` parameter of the recursor's type.
///     `offset` is the number of binders between the root of the induction rule and the use of the motive.
///     `indices` are the indices to the ADT instance that this motive is for.
///     `val` is the ADT instance that this motive is for.
fn calculate_constructor_induction_rule(
    adt_num_params: usize,
    get_adt_param: impl Fn(usize, usize) -> TypedTermKind,
    constructor: &AdtConstructor,
    reindex: impl Fn(usize, &TypedTerm) -> TypedTerm,
    motive: impl Fn(usize, Vec<TypedTerm>, TypedTerm) -> TypedTerm,
) -> TypedTerm {
    let mut induction_rule_params: Vec<_> = constructor
        .params
        .iter()
        .enumerate()
        .map(|(i, param)| TypedBinder {
            name: param.name,
            ty: reindex(i, &param.ty),
        })
        .collect();

    generate_inductive_parameter_principles(
        &constructor,
        &mut induction_rule_params,
        adt_num_params,
        &reindex,
        &motive,
    );

    let num_params = induction_rule_params.len();

    let output = calculate_constructor_induction_rule_output(
        &constructor,
        adt_num_params,
        |i| get_adt_param(i, num_params),
        |i| TypedTermKind::bound_variable(num_params - i - 1, constructor.params[i].name),
        |term| {
            reindex(
                induction_rule_params.len(),
                &term.clone_incrementing(0, induction_rule_params.len() - constructor.params.len()),
            )
        },
        |indices, val| motive(num_params, indices, val),
    );

    TypedTerm::make_telescope(induction_rule_params.clone(), output)
}

/// Generates the inductive principles for a specific constructor
///
/// # Parameters
/// * `constructor`: The constructor whose induction rule is being calculated
/// * `recursor_params`: Where to add the new parameters
/// * `adt_num_params`: The number of parameters of the ADT whose recursor is being generated
/// * `reindex(binders, term)`: Clones a term while re-indexing binders referring to ADT parameters.
///     `binders` is the number of binders between the source term and the root of the constructor's type.
/// * `motive(offset, indices, val)` : Gets a term referring to an application of the
///     `motive` parameter of the recursor's type.
///     `offset` is the number of binders between the root of the induction rule and the use of the motive.
///     `indices` are the indices to the ADT instance that this motive is for.
///     `val` is the ADT instance that this motive is for.
fn generate_inductive_parameter_principles(
    constructor: &AdtConstructor,
    induction_rule_params: &mut Vec<TypedBinder>,
    adt_num_params: usize,
    reindex: impl Fn(usize, &TypedTerm) -> TypedTerm,
    motive: impl Fn(usize, Vec<TypedTerm>, TypedTerm) -> TypedTerm,
) {
    // An iterator destructuring all the constructor's inductive parameters
    let inductive_params = constructor
        .params
        .iter()
        .enumerate()
        .filter_map(|(i, param)| match &param.kind {
            AdtConstructorParamKind::Inductive {
                parameters,
                indices,
            } => Some((i, param.name, parameters, indices)),
            AdtConstructorParamKind::NonInductive(_) => None,
        });

    for (param_index, name, param_params, param_indices) in inductive_params {
        let param_val = TypedTerm::bound_variable(
            param_params.len(),
            name,
            reindex(
                induction_rule_params.len() + param_params.len(),
                &constructor.params[param_index].ty.clone_incrementing(
                    0,
                    induction_rule_params.len() - param_index + param_params.len(),
                ),
            ),
        );

        let ty = calculate_inductive_parameter_principle(
            param_params,
            &param_indices[adt_num_params..],
            |binders, term| {
                reindex(
                    induction_rule_params.len() + binders,
                    &term.clone_incrementing(binders, induction_rule_params.len() - param_index),
                )
            },
            |offset, indices, val| motive(induction_rule_params.len() + offset, indices, val),
            param_val,
        );

        induction_rule_params.push(TypedBinder { name, ty })
    }
}

/// Generates the part of a recursor's type corresponding to a specific inductive parameter
/// in a specific constructor.
///
/// The format of this type is `<param_params> -> motive <indices> (<param value> <indices>)`
///
/// # Parameters
/// * `param_params`: The parameters to this constructor parameter
/// * `param_indices`: The indices to the output of this parameter, not including the ADT parameters.
/// * `reindex(binders, term)`: Clones a term while re-indexing binders referring to ADT parameters.
///     `binders` is the number of binders between the source term and the root of the inductive parameter.
/// * `motive(offset, indices, val)` : Gets a term referring to an application of the
///     `motive` parameter of the recursor's type.
///     `offset` is the number of binders between the root of the inductive parameter principle and the use of the motive.
///     `indices` are the indices to the ADT instance that this motive is for.
///     `val` is the ADT instance that this motive is for.
/// * `param_val`: The constructor parameter whose inductive principle is being calculated.
fn calculate_inductive_parameter_principle(
    param_params: &[TypedBinder],
    param_indices: &[TypedTerm],
    reindex: impl Fn(usize, &TypedTerm) -> TypedTerm,
    motive: impl Fn(usize, Vec<TypedTerm>, TypedTerm) -> TypedTerm,
    param_val: TypedTerm,
) -> TypedTerm {
    // Re-index the parameter's parameters
    let param_param_binders = param_params
        .iter()
        .enumerate()
        .map(|(i, param)| TypedBinder {
            name: param.name,
            ty: reindex(i, &param.ty),
        });

    // Re-index the parameter's indices
    let param_indices = param_indices
        .iter()
        .map(|index| reindex(param_params.len(), index))
        .collect();

    // The inductive parameter to `motive`, which is an application of the local variable
    // representing this parameter
    let inductive_val = TypedTerm::make_application_stack(
        param_val,
        param_params.iter().enumerate().map(|(i, param)| {
            TypedTermKind::bound_variable(param_params.len() - i - 1, param.name)
        }),
    );

    let motive = motive(param_params.len(), param_indices, inductive_val);

    TypedTerm::make_telescope(param_param_binders, motive)
}

/// Calculates the output of the induction rule for a constructor
///
/// # Parameters
/// * `constructor`: The constructor whose induction rule is being generated
/// * `adt_num_params`: The number of parameters or the ADT whose recursor is being generated
/// * `get_adt_param(i)`: Gets a term referring to the `i`th ADT parameter
/// * `get_constructor_param(i)`: Gets a term referring to the `i`th constructor parameter
/// * `reindex(term)`: Increments the binders in a term to account for additional binders
/// * `motive(indices, val)`: Gets a [`TypedTerm`] referring to an application of the
///     `motive` parameter of the recursor's type.
///     `indices` are the indices to the ADT instance that this motive is for.
///     `val` is the ADT instance that this motive is for.
fn calculate_constructor_induction_rule_output(
    constructor: &AdtConstructor,
    adt_num_params: usize,
    get_adt_param: impl Fn(usize) -> TypedTermKind,
    get_constructor_param: impl Fn(usize) -> TypedTermKind,
    reindex: impl Fn(&TypedTerm) -> TypedTerm,
    motive: impl Fn(Vec<TypedTerm>, TypedTerm) -> TypedTerm,
) -> TypedTerm {
    let motive_indices = constructor
        .indices
        .iter()
        .skip(adt_num_params) // Skip the ADT parameters as these are not given to the motive
        .map(reindex)
        .collect();

    // The constructor applied to the ADT params and the constructor's parameters
    let constructor_application = TypedTerm::make_application_stack(
        constructor.constant.clone(),
        (0..adt_num_params)
            .map(get_adt_param)
            .chain((0..constructor.params.len()).map(get_constructor_param)),
    );

    motive(motive_indices, constructor_application)
}

impl Adt {
    pub fn recursor_num_parameters(&self) -> usize {
        self.header.parameters.len() + 1 + self.constructors.len() + self.header.indices.len() + 1
    }

    pub fn recursor_value_param_index(&self) -> usize {
        self.recursor_num_parameters() - 1
    }

    pub fn recursor_constructor_param_index(&self, param: usize) -> usize {
        self.header.parameters.len() + 1 + param
    }
}
