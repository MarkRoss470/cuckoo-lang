data Nat : Type where
  | zero : Nat
  | succ : Nat -> Nat

data Dep : (Nat -> Nat -> Nat) -> Type where

def f1 : Nat -> Nat -> Nat := fun (x : Nat) => fun (y : Nat) => x
def f2 : Nat -> Nat -> Nat := fun (y : Nat) => fun (x : Nat) => y
def f3 : Nat -> Nat -> Nat := fun (x : Nat) => fun (y : Nat) => y
def f4 : Nat -> Nat -> Nat := fun (y : Nat) => fun (x : Nat) => x

-- Good
def d12 (D : Dep f1) : Dep f2 := D
def d21 (D : Dep f2) : Dep f1 := D
def d34 (D : Dep f3) : Dep f4 := D
def d43 (D : Dep f4) : Dep f3 := D

-- Error
def d13 (D : Dep f1) : Dep f3 := D
