data Nat : Type where
  | zero : Nat
  | succ : Nat -> Nat

data F : Type where
  | c1 : F
  | c2 : (Nat -> F) -> F

def F.r (f : F) : Nat := F.rec.{1}
    (fun (_ : F) => Nat)
    Nat.zero
    (fun (f : Nat -> F) (h : Nat -> Nat) => Nat.succ (h Nat.zero))
    f

def n1 : Nat := F.r F.c1
def n2 : Nat := F.r (F.c2 (fun (_ : Nat) => F.c1))
def n3 : Nat := F.r (F.c2 (fun (_ : Nat) => F.c2 (fun (_ : Nat) => F.c1)))

data Dep : Nat -> Type where

def d1 (D : Dep n1) : Dep Nat.zero := D
def d2 (D : Dep n2) : Dep (Nat.succ Nat.zero) := D
def d3 (D : Dep n3) : Dep (Nat.succ (Nat.succ Nat.zero)) := D