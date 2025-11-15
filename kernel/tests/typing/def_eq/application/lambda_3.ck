data Nat : Type where
  | zero : Nat
  | succ : Nat -> Nat

data Dep : (Nat -> Nat) -> Type where

def d1 (D : Dep ((fun (f : Nat -> Nat) => fun (x : Nat) => f (f x)) (fun (x : Nat) => Nat.succ x)))
        : Dep (fun (x : Nat) => Nat.succ (Nat.succ x))
        := D

