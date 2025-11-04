data T : Type where
  | c1 : T
  | c2 : T

data Dep : T -> Type where

axiom A : T
axiom B : T

def a_not_def_eq_b (d : Dep A) : Dep B := d
