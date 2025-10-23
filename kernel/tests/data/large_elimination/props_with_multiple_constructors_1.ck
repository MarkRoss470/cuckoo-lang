data SomeTy : Prop where
  | c1 : SomeTy
  | c2 : SomeTy

-- This `Prop` judgement is wrong, but never reached because the level error is encountered first
def some_ty_rec : Prop := SomeTy.rec.{1}