data T : Type where
  | c1 : T
  | c2 : T

data U : Type where
  | c1 : U
  | c2 : U

data Dep : U -> Type where

def a1 : U := T.rec.{1}
    (fun (_ : T) => U)
    U.c1
    U.c2
    T.c1

def a2 : U := T.rec.{1}
    (fun (_ : T) => U)
    U.c1
    U.c2
    T.c2

def a1_def_eq_c1 (D : Dep a1) : Dep U.c1 := D
def a2_def_eq_c2 (D : Dep a2) : Dep U.c2 := D
