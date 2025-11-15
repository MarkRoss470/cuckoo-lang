-- The following three ways to define a function are all equivalent
def d1 (T : Type) (x : T) (y : T) : T := x
def d2 : (T : Type) -> T -> T -> T := fun (T : Type) (x : T) (y : T) => x
def d3 : (T : Type) -> (_ : T) -> (y : T) -> T := fun (T : Type) => fun (x : T) => fun (_ : T) => x

data Dep : ((T : Type) -> T -> T -> T) -> Type where

def d12 (D : Dep d1) : Dep d2 := D
def d13 (D : Dep d1) : Dep d3 := D
def d23 (D : Dep d2) : Dep d3 := D
