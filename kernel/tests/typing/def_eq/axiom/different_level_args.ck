data T : Type where
  | c : T

data Dep : T -> Type where

axiom A.{u} : T

def a_0_ne_a_1 (d : Dep A.{0}) : Dep A.{1} := d
