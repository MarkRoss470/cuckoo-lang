data Nat : Type where
  | zero : Nat
  | succ : Nat -> Nat

data Dep : Nat -> Type where

def d1 (D : Dep ((fun (n : Nat) => n) Nat.zero)) : Dep Nat.zero := D
def d2 (D : Dep ((fun (n : Nat) => Nat.succ n) (Nat.succ Nat.zero))) : Dep (Nat.succ (Nat.succ Nat.zero)) := D
def d3 (f : Nat -> Nat) (D : Dep ((fun (n : Nat) => f n) Nat.zero)) : Dep (f Nat.zero) := D
def d4 (f : Nat -> Nat) (D : Dep ((fun (n : Nat) => f (Nat.succ n)) (f Nat.zero))) : Dep (f (Nat.succ (f Nat.zero))) := D

def d5 (D : Dep ((fun (f : Nat -> Nat) => f (f Nat.zero)) (fun (x : Nat) => Nat.succ x)))
        : Dep (Nat.succ (Nat.succ Nat.zero))
        := D