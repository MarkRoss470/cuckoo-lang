data SomeProp1 : Prop where
  | c1 : SomeProp1
  | c2 : SomeProp1

data SomeProp2 : Prop where
  | c : SomeProp1 -> SomeProp2

-- This `Prop` judgement is wrong, but never reached because the level error is encountered first
def some_prop_rec : Prop := SomeProp2.rec