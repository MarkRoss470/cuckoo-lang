data Nat : Type where
  | zero : Nat
  | succ : Nat -> Nat

data Vec.{u} (T : Type u) : Nat -> Type u where
  | nil : Vec T Nat.zero
  | cons : (n : Nat) -> T -> Vec T n -> Vec T (Nat.succ n)

def a (m : Nat) (n : Nat) (f : Vec.{0} Nat m -> Nat) (v : Vec.{0} Nat n) : Nat := f v