data SomeProp : Prop where
  | c : SomeProp -> SomeProp

-- This `Prop` judgement is wrong, but never reached because the level error is encountered first
def some_prop_rec : Prop := SomeProp.rec