data Nat : Type where
  | zero : Nat
  | succ : Nat -> Nat

def nat_rec.{m} :
    (motive : Nat -> Sort m)
    -> (zero : motive Nat.zero)
    -> (succ : (x : Nat) -> motive x -> motive (Nat.succ x))
    -> (x : Nat)
    -> motive x
    := Nat.rec.{m}