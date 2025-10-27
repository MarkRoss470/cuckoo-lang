data Unit : Type where
  | mk : Unit

data Invalid : Unit.mk -> Type where