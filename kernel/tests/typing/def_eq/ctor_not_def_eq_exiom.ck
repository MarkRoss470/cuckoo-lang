data T : Type where
  | c1 : T
  | c2 : T

data Dep : T -> Type where

axiom A : T

def ctor_not_def_eq_a (d : Dep T.c1) : Dep A := d
