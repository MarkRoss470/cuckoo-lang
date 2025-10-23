data SomeTy : Prop -> Prop where

data Invalid : Prop where
  | c : SomeTy Invalid -> Invalid