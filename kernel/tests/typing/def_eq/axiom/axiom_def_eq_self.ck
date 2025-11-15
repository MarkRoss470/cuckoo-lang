data T : Type where
  | c1 : T
  | c2 : T

data Dep : T -> Type where

axiom A : T

def a_def_eq_a (d : Dep A) : Dep A := d
