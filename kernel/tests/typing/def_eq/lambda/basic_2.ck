data T : Type where

def f1 : T -> T -> T := fun (x : T) => (fun (y : T) => fun (z : T) => x) x
def f2 : T -> T -> T := fun (x : T) => (fun (y : T) => fun (z : T) => y) x

def f3 : T -> T -> T := fun (x : T) => (fun (y : T) => fun (z : T) => z) x

data Dep : (T -> T -> T) -> Type where

-- Good
def d11 (D : Dep f1) : Dep f1 := D
def d12 (D : Dep f1) : Dep f2 := D
def d21 (D : Dep f2) : Dep f1 := D
def d22 (D : Dep f2) : Dep f2 := D

-- Error
def d13 (D : Dep f1) : Dep f3 := D