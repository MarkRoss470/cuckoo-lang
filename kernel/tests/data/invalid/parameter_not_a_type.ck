data Unit : Type where
  | mk : Unit

data Invalid (x : Unit.mk) : Type where