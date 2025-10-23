data SomeProp (P : Prop) : Prop where
  | c : P -> SomeProp P

-- This `Prop` judgement is wrong, but never reached because the level error is encountered first
def some_prop_rec : Prop := SomeProp.rec