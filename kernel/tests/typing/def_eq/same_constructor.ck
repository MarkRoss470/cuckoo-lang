data T : Type where
  | c1 : T
  | c2 : T

data Dep : T -> Type where

def d (D : Dep T.c1) : Dep T.c1 := D