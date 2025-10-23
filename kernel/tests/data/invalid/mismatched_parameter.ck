data SomeTy : Type where

data Invalid (T : Type) : Type where
  | c : Invalid SomeTy