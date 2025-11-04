data T : Type where
  | c1 : T
  | c2 : T

data Dep : T -> Type where

axiom A : T

def a_not_def_eq_ctor (d : Dep A) : Dep T.c1 := d
