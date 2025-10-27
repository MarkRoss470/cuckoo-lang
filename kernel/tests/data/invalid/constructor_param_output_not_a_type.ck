data Unit : Type where
  | mk : Unit

data Invalid : Type where
  | c : (Invalid -> Unit.mk) -> Invalid