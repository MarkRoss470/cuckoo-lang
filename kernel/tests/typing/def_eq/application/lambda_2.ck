data Nat : Type where
  | zero : Nat
  | succ : Nat -> Nat

data Dep : Nat -> Type where

def d3 (f : Nat -> Nat) (g : Nat -> Nat)
        (D : Dep ((fun (n : Nat) => f (Nat.succ n)) (f Nat.zero)))
        : Dep (g (Nat.succ (f Nat.zero))) := D

