data Nat : Type where
  | zero : Nat
  | succ : Nat -> Nat

data SomeProp : Nat -> Prop where
  | c : (n : Nat) -> SomeProp (Nat.succ n)

-- Even though `succ` is an injection, `SomeProp` is not large eliminating because `n` is not used verbatim in an index
def some_prop_rec : Prop := SomeProp.rec.{1}