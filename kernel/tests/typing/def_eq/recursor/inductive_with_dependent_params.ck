data Nat : Type where
  | zero : Nat
  | succ : Nat -> Nat

data Dep : Nat -> Type where
  | c : (n : Nat) -> Dep n

data F : Type where
  | c1 : F
  | c2 : (n : Nat) -> (Dep n -> F) -> F

def F.r (f : F) : Nat := F.rec.{1}
    (fun (_ : F) => Nat)
    Nat.zero
    (fun (n : Nat) (f : Dep n -> F) (h : Dep n -> Nat) => Nat.succ (h (Dep.c n)))
    f

def n1 : Nat := F.r F.c1
def n2 : Nat := F.r (F.c2 Nat.zero (fun (_ : Dep Nat.zero) => F.c1))
def n3 : Nat := F.r (F.c2 Nat.zero (fun (_ : Dep Nat.zero) => F.c2 Nat.zero (fun (_ : Dep Nat.zero) => F.c1)))

def d1 (D : Dep n1) : Dep Nat.zero := D
def d2 (D : Dep n2) : Dep (Nat.succ Nat.zero) := D
def d3 (D : Dep n3) : Dep (Nat.succ (Nat.succ Nat.zero)) := D