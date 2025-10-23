data Nat : Type where
  | zero : Nat
  | succ : Nat -> Nat

data SomeProp : Nat -> Prop where
  | c : (n : Nat) -> SomeProp n

def some_prop_rec : Prop := SomeProp.rec