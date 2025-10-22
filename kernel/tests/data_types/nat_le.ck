data Nat : Type where
  | zero : Nat
  | succ : Nat -> Nat

data Nat.Le (m : Nat) : Nat -> Prop where
  | refl : Le m m
  | step : (n : Nat) -> Le m n -> Le m (Nat.succ n)

def nat_le_rec :
    (m : Nat)
    -> (motive : (n : Nat) -> Nat.Le m n -> Prop)
    -> (refl : motive m (Nat.Le.refl m))
    -> (step : (n : Nat) -> (h : Nat.Le m n) -> motive n h -> motive (Nat.succ n) (Nat.Le.step m n h))
    -> (n : Nat)
    -> (h : Nat.Le m n)
    -> motive n h
    := Nat.Le.rec