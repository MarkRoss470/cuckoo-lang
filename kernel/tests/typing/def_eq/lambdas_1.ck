data T : Type where

def f1 : T -> T := fun (x : T) => (fun (y : T) => x) x
def f2 : T -> T := fun (x : T) => (fun (y : T) => y) x

data Dep : (T -> T) -> Type where

def d (D : Dep f1) : Dep f2 := D