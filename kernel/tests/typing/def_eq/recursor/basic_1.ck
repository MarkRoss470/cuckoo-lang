data T : Type where
  | c : T

data U : Type where
  | c : U

data Dep : U -> Type where

def a : U := T.rec.{1}
    (fun (_ : T) => U)
    U.c
    T.c

def a_def_eq_c (D : Dep a) : Dep U.c := D