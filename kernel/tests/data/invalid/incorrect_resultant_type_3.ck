data T : Type where
  | c : T

data U : T -> T -> Prop where

data Invalid : T -> Type 1 where
  | c : U T.c T.c