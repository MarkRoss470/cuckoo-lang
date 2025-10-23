data Nat : Type where
  | zero : Nat
  | succ : Nat -> Nat

data SomeProp : Nat -> Nat -> Prop where
  | c : (m : Nat) -> (n : Nat) -> SomeProp n m

def some_prop_rec : Prop := SomeProp.rec