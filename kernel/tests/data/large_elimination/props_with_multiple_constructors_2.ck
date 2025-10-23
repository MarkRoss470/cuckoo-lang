data False : Prop where

data SomeTy : Prop where
  | c1 : False -> SomeTy
  | c2 : False -> SomeTy

-- Even though neither of `SomeTy`'s constructors are actually inhabited, `SomeTy` is not large eliminating.
-- This `Prop` judgement is wrong, but never reached because the level error is encountered first
def some_ty_rec : Prop := SomeTy.rec.{1}