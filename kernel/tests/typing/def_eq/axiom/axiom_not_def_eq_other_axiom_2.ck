data T : Type where
  | c : T

data Dep : T -> Type where

axiom A : T
axiom B : T

def a_not_def_eq_b (d : Dep A) : Dep B := d
