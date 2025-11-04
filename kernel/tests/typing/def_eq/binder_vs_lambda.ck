def d1 (T : Type) (x : T) (y : T) : T := x
def d2 : (T : Type) -> T -> T -> T := fun (T : Type) (x : T) (y : T) => x

data Dep : ((T : Type) -> T -> T -> T) -> Type where

def fun_equiv (D : Dep d1) : Dep d2 := D