use super::*;
use crate::parser::ast::item::Item;
use crate::parser::ast::parse_file;
use crate::typeck::level::LevelArgs;
use crate::typeck::tests::{assert_type_checks, assert_type_error};

macro_rules! resolve_adt {
    ($source: expr, $ast: ident, $env: ident, $res: ident, ) => {
        let (interner, file) = crate::parse_file($source).unwrap();
        let Some(Item::DataDefinition($ast)) = &file.items.last() else {
            panic!();
        };
        let mut $env = TypingEnvironment::new(interner);
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
    let ty = TypedTerm::sort_literal(Level::constant(1));
    let nat = TypedTerm::adt_name(res.header.index, ty.clone());

    // Check the header
    assert_eq!(ast.name, res.header.name);
    assert_eq!(res.header.level_params, LevelParameters::new(&[]));
    assert!(res.header.parameters.is_empty());
    assert!(res.header.indices.is_empty());
    assert_eq!(res.header.sort, Level::constant(1));
    assert_eq!(res.header.family, ty);
    assert_eq!(res.header.is_prop, false);
    assert_eq!(res.is_large_eliminating, true);

    // Check the constructors
    let [zero, succ] = res.constructors.as_slice() else {
        panic!("Wrong number of constructors");
    };

    assert!(zero.params.is_empty());
    assert!(zero.indices.is_empty());
    assert_eq!(zero.type_without_adt_params, nat.clone());

    assert_eq!(
        succ.params,
        vec![AdtConstructorParam {
            name: None,
            ty: TypedTerm::adt_name(AdtIndex(0), ty.clone()),
            kind: AdtConstructorParamKind::Inductive {
                parameters: vec![],
                indices: vec![]
            }
        }]
    );
    assert!(succ.indices.is_empty());
    assert_eq!(
        succ.type_without_adt_params,
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

    // Check the type of the recursor
    let level_u = Level::parameter(0, Identifier::from_str("u", &mut env.interner.borrow_mut()));
    let sort_u = TypedTerm::sort_literal(level_u.clone());
    let args_u = LevelArgs(vec![level_u]);
    let recursor = env
        .resolve_path(
            id_nat
                .clone()
                .append(env.interner.borrow().kw_rec())
                .borrow(),
            &args_u,
        )
        .unwrap();
    let id_motive = Identifier::from_str("motive", &mut env.interner.borrow_mut());

    let motive_ty = TypedTerm::make_pi_type(
        TypedBinder {
            name: None,
            ty: nat.clone(),
        },
        sort_u.clone(),
    );
    let motive = |i, arg| {
        TypedTerm::make_application(
            TypedTerm::bound_variable(i, Some(id_motive), motive_ty.clone()),
            arg,
            sort_u.clone(),
        )
    };

    let case_zero = motive(0, zero_const.clone());
    let case_succ = TypedTerm::make_pi_type(
        TypedBinder {
            name: None,
            ty: nat.clone(),
        },
        TypedTerm::make_pi_type(
            TypedBinder {
                name: None,
                ty: motive(2, TypedTerm::bound_variable(0, None, nat.clone())),
            },
            motive(
                3,
                TypedTerm::make_application(
                    succ_const.clone(),
                    TypedTerm::bound_variable(1, None, nat.clone()),
                    nat.clone(),
                ),
            ),
        ),
    );

    let recursor_expected = TypedTerm::adt_recursor(
        AdtIndex(0),
        TypedTerm::make_pi_type(
            TypedBinder {
                name: Some(id_motive),
                ty: motive_ty.clone(),
            },
            TypedTerm::make_pi_type(
                TypedBinder {
                    name: Some(zero.name),
                    ty: case_zero,
                },
                TypedTerm::make_pi_type(
                    TypedBinder {
                        name: Some(succ.name),
                        ty: case_succ,
                    },
                    TypedTerm::make_pi_type(
                        TypedBinder {
                            name: None,
                            ty: nat.clone(),
                        },
                        motive(3, TypedTerm::bound_variable(0, None, nat.clone())),
                    ),
                ),
            ),
        ),
    );

    assert_eq!(recursor, recursor_expected);
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
    let args_u = LevelArgs(vec![level_u.clone()]);

    let t_type = |i| TypedTerm::bound_variable(i, Some(id_t), type_u.clone());
    let list_ty = TypedTerm::make_pi_type(
        TypedBinder {
            name: Some(id_t),
            ty: type_u.clone(),
        },
        type_u.clone(),
    );
    let list = TypedTerm::adt_name(res.header.index, list_ty);
    let list_t = |i| TypedTerm::make_application(list.clone(), t_type(i), type_u.clone());

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
    assert_eq!(nil.indices, vec![t_type(0)]);

    assert_eq!(
        cons.params,
        vec![
            AdtConstructorParam {
                name: None,
                ty: t_type(0),
                kind: AdtConstructorParamKind::NonInductive(t_type(0))
            },
            AdtConstructorParam {
                name: None,
                ty: list_t(1),
                kind: AdtConstructorParamKind::Inductive {
                    parameters: vec![],
                    indices: vec![TypedTerm::bound_variable(1, Some(id_t), type_u.clone())]
                }
            }
        ]
    );
    assert_eq!(cons.indices, vec![t_type(2)]);

    // Check the generated constants
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

    let cons_const = env
        .resolve_path(id_list.clone().append(cons.name).borrow(), &args_u)
        .unwrap();

    assert_eq!(
        cons_const,
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
                        ty: t_type(0)
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

    // Check the type of the recursor
    let level_m = Level::parameter(1, Identifier::from_str("m", &mut env.interner.borrow_mut()));
    let sort_m = TypedTerm::sort_literal(level_m.clone());
    let args_u = LevelArgs(vec![level_u, level_m]);
    let recursor = env
        .resolve_path(
            id_list
                .clone()
                .append(env.interner.borrow().kw_rec())
                .borrow(),
            &args_u,
        )
        .unwrap();
    let id_motive = Identifier::from_str("motive", &mut env.interner.borrow_mut());

    let motive_ty = |i| {
        TypedTerm::make_pi_type(
            TypedBinder {
                name: None,
                ty: list_t(i),
            },
            sort_m.clone(),
        )
    };
    let motive = |i, arg| {
        TypedTerm::make_application(
            TypedTerm::bound_variable(i, Some(id_motive), motive_ty(i + 1)),
            arg,
            sort_m.clone(),
        )
    };

    let case_nil = motive(
        0,
        TypedTerm::make_application(
            nil_const.clone(),
            TypedTerm::bound_variable(1, Some(id_t), type_u.clone()),
            list_t(1),
        ),
    );
    let case_cons = TypedTerm::make_pi_type(
        TypedBinder {
            name: None,
            ty: TypedTerm::bound_variable(2, Some(id_t), type_u.clone()),
        },
        TypedTerm::make_pi_type(
            TypedBinder {
                name: None,
                ty: list_t(3),
            },
            TypedTerm::make_pi_type(
                TypedBinder {
                    name: None,
                    ty: motive(3, TypedTerm::bound_variable(0, None, list_t(4))),
                },
                motive(
                    4,
                    TypedTerm::make_application_stack(
                        cons_const.clone(),
                        [
                            TypedTermKind::BoundVariable {
                                index: 5,
                                name: Some(id_t),
                            },
                            TypedTermKind::BoundVariable {
                                index: 2,
                                name: None,
                            },
                            TypedTermKind::BoundVariable {
                                index: 1,
                                name: None,
                            },
                        ],
                    ),
                ),
            ),
        ),
    );

    let recursor_expected = TypedTerm::adt_recursor(
        AdtIndex(0),
        TypedTerm::make_pi_type(
            TypedBinder {
                name: Some(id_t),
                ty: type_u.clone(),
            },
            TypedTerm::make_pi_type(
                TypedBinder {
                    name: Some(id_motive),
                    ty: motive_ty(0),
                },
                TypedTerm::make_pi_type(
                    TypedBinder {
                        name: Some(nil.name),
                        ty: case_nil,
                    },
                    TypedTerm::make_pi_type(
                        TypedBinder {
                            name: Some(cons.name),
                            ty: case_cons,
                        },
                        TypedTerm::make_pi_type(
                            TypedBinder {
                                name: None,
                                ty: list_t(3),
                            },
                            motive(3, TypedTerm::bound_variable(0, None, list_t(4))),
                        ),
                    ),
                ),
            ),
        ),
    );

    assert_eq!(recursor, recursor_expected);
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
    let args_u = LevelArgs(vec![level_u.clone()]);

    let t = |t_offset| TypedTerm::bound_variable(t_offset, Some(id_t), sort_u.clone());
    let x = |x_offset| TypedTerm::bound_variable(x_offset, Some(id_x), t(x_offset + 1));

    let prop = TypedTerm::sort_literal(Level::zero());

    // T -> Prop
    let t_to_prop = |t_offset| {
        TypedTerm::make_pi_type(
            TypedBinder {
                name: None,
                ty: t(t_offset),
            },
            prop.clone(),
        )
    };
    // (x : T) -> T -> Prop
    let x_to_t_to_prop = |t_offset| {
        TypedTerm::make_pi_type(
            TypedBinder {
                name: Some(id_x),
                ty: t(t_offset),
            },
            t_to_prop(t_offset + 1).clone(),
        )
    };
    // (T : Sort u) -> (x : T) -> T -> Prop
    let t_to_x_to_t_to_prop = TypedTerm::make_pi_type(
        TypedBinder {
            name: Some(id_t),
            ty: sort_u.clone(),
        },
        x_to_t_to_prop(0).clone(),
    );
    let eq = |t_offset, x, y| {
        TypedTerm::make_application(
            TypedTerm::make_application(
                TypedTerm::make_application(
                    TypedTerm::adt_name(res.header.index, t_to_x_to_t_to_prop.clone()),
                    t(t_offset),
                    x_to_t_to_prop(t_offset),
                ),
                x,
                t_to_prop(t_offset),
            ),
            y,
            prop.clone(),
        )
    };

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
                ty: t(0),
            }
        ]
    );
    assert_eq!(
        res.header.indices,
        vec![TypedBinder {
            name: None,
            ty: t(1)
        }]
    );
    assert_eq!(res.header.sort, Level::zero());

    assert_eq!(res.header.family, t_to_prop(1));
    assert_eq!(res.header.is_prop, true);
    assert_eq!(res.is_large_eliminating, true);

    // Check the constructor
    let [refl] = res.constructors.as_slice() else {
        panic!("Wrong number of constructors");
    };

    assert!(refl.params.is_empty());
    assert_eq!(refl.indices, vec![t(1), x(0), x(0)]);

    // Check the generated constants
    let type_constructor = env.resolve_path(ast.name.borrow(), &args_u).unwrap();
    assert_eq!(
        type_constructor,
        TypedTerm::adt_name(res.header.index, t_to_x_to_t_to_prop.clone())
    );

    let refl_const = env
        .resolve_path(ast.name.clone().append(refl.name).borrow(), &args_u)
        .unwrap();

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
                    ty: t(0),
                },
                eq(1, x(0), x(0)),
            ),
        ),
    );

    assert_eq!(refl_const, refl_const_expected);

    // Check the type of the recursor
    let level_m = Level::parameter(1, Identifier::from_str("m", &mut env.interner.borrow_mut()));
    let sort_m = TypedTerm::sort_literal(level_m.clone());
    let args_u = LevelArgs(vec![level_u, level_m]);
    let recursor = env
        .resolve_path(
            ast.name
                .clone()
                .append(env.interner.borrow().kw_rec())
                .borrow(),
            &args_u,
        )
        .unwrap();
    let id_motive = Identifier::from_str("motive", &mut env.interner.borrow_mut());

    let motive_ty = |x_offset| {
        TypedTerm::make_pi_type(
            TypedBinder {
                name: None,
                ty: t(x_offset + 1),
            },
            TypedTerm::make_pi_type(
                TypedBinder {
                    name: None,
                    ty: eq(
                        x_offset + 2,
                        x(x_offset + 1),
                        TypedTerm::bound_variable(0, None, t(x_offset + 2)),
                    ),
                },
                sort_m.clone(),
            ),
        )
    };
    let motive = |motive_offset, x, arg| {
        TypedTerm::make_application_stack(
            TypedTerm::bound_variable(motive_offset, Some(id_motive), motive_ty(motive_offset + 1)),
            vec![x, arg],
        )
    };

    let case_refl = motive(
        0,
        x(1).term,
        TypedTerm::make_application_stack(refl_const_expected, vec![t(2).term, x(1).term]).term,
    );

    let recursor_expected = TypedTerm::adt_recursor(
        res.header.index,
        TypedTerm::make_pi_type(
            TypedBinder {
                name: Some(id_t),
                ty: sort_u.clone(),
            },
            TypedTerm::make_pi_type(
                TypedBinder {
                    name: Some(id_x),
                    ty: t(0),
                },
                TypedTerm::make_pi_type(
                    TypedBinder {
                        name: Some(id_motive),
                        ty: motive_ty(0),
                    },
                    TypedTerm::make_pi_type(
                        TypedBinder {
                            name: Some(refl.name),
                            ty: case_refl,
                        },
                        TypedTerm::make_pi_type(
                            TypedBinder {
                                name: None,
                                ty: t(3),
                            },
                            TypedTerm::make_pi_type(
                                TypedBinder {
                                    name: None,
                                    ty: eq(4, x(3), TypedTerm::bound_variable(0, None, t(4))),
                                },
                                motive(
                                    3,
                                    TypedTermKind::BoundVariable {
                                        index: 1,
                                        name: None,
                                    },
                                    TypedTermKind::BoundVariable {
                                        index: 0,
                                        name: None,
                                    },
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );

    assert_eq!(recursor, recursor_expected);
}

#[test]
fn test_adt_recursors() {
    assert_type_checks!(
        "data True : Prop where
          | intro : True
        
        def true_rec.{m} :
            (motive : True -> Sort m)
            -> (intro : motive True.intro)
            -> (t : True)
            -> motive t
            := True.rec.{m}"
    );

    assert_type_checks!(
        "data False : Prop where

        def false_rec.{m} :
            (motive : False -> Sort m)
            -> (f : False)
            -> motive f
            := False.rec.{m}"
    );

    assert_type_checks!(
        "data Nat : Type where
          | zero : Nat
          | succ : Nat -> Nat
    
        def nat_rec.{m} :
            (motive : Nat -> Sort m)
            -> (zero : motive Nat.zero)
            -> (succ : (x : Nat) -> motive x -> motive (Nat.succ x))
            -> (x : Nat)
            -> motive x
            := Nat.rec.{m}

        data Nat.Le (x : Nat) : Nat -> Prop where
          | refl : Le x x
          | step : (y : Nat) -> Le x y -> Le x (Nat.succ y)

        -- Nat.Le is not large eliminating so the recursor does not have any level parameters
        def le_rec :
            (x : Nat)
            -> (motive : (y : Nat) -> Nat.Le x y -> Prop)
            -> (refl : motive x (Nat.Le.refl x))
            -> (step : (y : Nat) -> (hy : Nat.Le x y) -> motive y hy -> motive (Nat.succ y) (Nat.Le.step x y hy))
            -> (y : Nat)
            -> (hy : Nat.Le x y)
            -> motive y hy
            := Nat.Le.rec
        "
    );

    assert_type_checks!(
        "data Nat : Type where
          | zero : Nat
          | succ : Nat -> Nat
    
        def nat_rec.{m} :
            (motive : Nat -> Sort m)
            -> (zero : motive Nat.zero)
            -> (succ : (x : Nat) -> motive x -> motive (Nat.succ x))
            -> (x : Nat)
            -> motive x
            := Nat.rec.{m}"
    );

    assert_type_checks!(
        "data List.{u} (T : Type u) : Type u where
          | nil : List T
          | cons : T -> List T -> List T
    
        def list_rec.{u, m} :
            (T : Type u)
            -> (motive : List.{u} T -> Sort m)
            -> (nil : motive (List.nil.{u} T))
            -> (cons : (x : T) -> (xs : List.{u} T) -> motive xs -> motive (List.cons.{u} T x xs))
            -> (l : List.{u} T)
            -> motive l
            := List.rec.{u, m}"
    );

    assert_type_checks!(
        "data Eq.{u} (T : Sort u) (x : T) : T -> Prop where
            | refl : Eq T x x
    
        def eq_rec.{u, m} :
            (T : Sort u)
            -> (x : T)
            -> (motive : (y : T) -> (Eq.{u} T x y) -> Sort m)
            -> (refl : motive x (Eq.refl.{u} T x))
            -> (y : T)
            -> (e : Eq.{u} T x y)
            -> motive y e
            := Eq.rec.{u, m}"
    );

    assert_type_checks!(
        "data Acc.{u} (T : Sort u) (R : T -> T -> Prop) : T -> Prop where
           | acc : (x : T) -> ((y : T) -> R y x -> Acc T R y) -> Acc T R x
    
         def acc_rec.{u, m} :
            (T : Sort u)
            -> (R : T -> T -> Prop)
            -> (motive : (x : T) -> Acc.{u} T R x -> Sort m)
            -> (acc :
              (x : T)
              -> (h : (y : T) -> (R y x) -> Acc.{u} T R y)
              -> ((y : T) -> (hy : R y x) -> motive y (h y hy))
              -> motive x (Acc.acc.{u} T R x h))
            -> (x : T)
            -> (a : Acc.{u} T R x)
            -> motive x a
            := Acc.rec.{u, m}"
    );
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
            found: TypedTerm::adt_name(AdtIndex(0), TypedTerm::sort_literal(Level::constant(1))),
            expected: TypedTerm::bound_variable(
                0,
                Some(Identifier::dummy_val(9)),
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
