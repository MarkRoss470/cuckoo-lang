data Nat : Type where
  | zero : Nat
  | succ : Nat -> Nat

data Dep : (Nat -> Nat) -> Type where

def d1 (D : Dep Nat.succ) : Dep (fun (n : Nat) => Nat.succ n) := D
def d2 (D : Dep (fun (n : Nat) => Nat.succ n)) : Dep Nat.succ := D
