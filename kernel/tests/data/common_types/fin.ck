data Nat : Type where
  | zero : Nat
  | succ : Nat -> Nat

data Fin : Nat -> Type where
  | zero : (n : Nat) -> Fin n
  | succ : (n : Nat) -> Fin n -> Fin (Nat.succ n)

def fin_rec.{m} :
    (motive : (n : Nat) -> Fin n -> Sort m)
    -> (zero : (n : Nat) -> motive n (Fin.zero n))
    -> (succ : (n : Nat)
        -> (f : Fin n)
        -> (h : motive n f)
        -> motive (Nat.succ n) (Fin.succ n f))
    -> (n : Nat)
    -> (f : Fin n)
    -> motive n f
    := Fin.rec.{m}