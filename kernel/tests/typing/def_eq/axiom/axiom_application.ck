data T : Type where
  | c : T

data Dep : T -> Type where

axiom A : T -> T
axiom B : T

def a_b_def_eq_a_b (d : Dep (A B)) : Dep (A B) := d
