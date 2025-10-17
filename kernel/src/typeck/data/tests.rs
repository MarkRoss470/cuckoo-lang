use super::*;
use crate::typeck::tests::{assert_type_checks, assert_type_error};

#[test]
fn test_adt_recursors() {
    assert_type_checks(
        "data True : Prop where
          | intro : True
        
        def true_rec.{m} :
            (motive : True -> Sort m)
            -> (intro : motive True.intro)
            -> (t : True)
            -> motive t
            := True.rec.{m}",
    );

    assert_type_checks(
        "data False : Prop where

        def false_rec.{m} :
            (motive : False -> Sort m)
            -> (f : False)
            -> motive f
            := False.rec.{m}",
    );

    assert_type_checks(
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

    assert_type_checks(
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
            := List.rec.{u, m}",
    );

    assert_type_checks(
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
            := Eq.rec.{u, m}",
    );

    assert_type_checks(
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
            := Acc.rec.{u, m}",
    );
}

#[test]
fn test_invalid_adt_definitions() {
    assert_type_error(
        "data False : Prop where

        data Ty : False where",
        TypeError::NotASortFamily(TypedTerm::adt_name(
            AdtIndex(0),
            TypedTerm::sort_literal(Level::zero()),
            LevelArgs::default(),
        )),
    );

    assert_type_error(
        "data Ty.{u} : Sort u where",
        TypeError::MayOrMayNotBeProp(Level::parameter(0, Identifier::dummy(0))),
    );

    assert_type_error(
        "data Ty : Type where
           | c : Prop
        ",
        TypeError::IncorrectConstructorResultantType {
            name: Identifier::dummy(6),
            found: TypedTerm::sort_literal(Level::zero()),
            expected: AdtIndex(0),
        },
    );

    assert_type_error(
        "data False : Prop where

        data Ty : Prop where
           | c : (Ty -> Prop) -> Ty",
        TypeError::InvalidLocationForAdtNameInConstructor(AdtIndex(1)),
    );

    assert_type_error(
        "data False : Prop where

        data Ty : Prop -> Prop where
           | c : Ty (Ty False)",
        TypeError::InvalidLocationForAdtNameInConstructor(AdtIndex(1)),
    );

    assert_type_error(
        "data False : Type where

        data Ty (T : Type) : Type where
           | constructor : Ty False",
        TypeError::MismatchedAdtParameter {
            found: TypedTerm::adt_name(
                AdtIndex(0),
                TypedTerm::sort_literal(Level::constant(1)),
                LevelArgs::default(),
            ),
            expected: TypedTerm::bound_variable(
                0,
                Some(Identifier::dummy(7)),
                TypedTerm::sort_literal(Level::constant(1)),
            )
            .term(),
        },
    );

    assert_type_error(
        "data Ty : Type where
           | c : Type -> Ty",
        TypeError::InvalidConstructorParameterLevel {
            ty: TypedTerm::sort_literal(Level::constant(1)),
            adt_level: Level::constant(1),
        },
    );
}
