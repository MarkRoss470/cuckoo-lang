data T.{u} (U : Sort u) : Type where

data Dep : Type -> Prop where

def d1.{u} (U : Sort u) (D : Dep (T.{u} U)) : Dep (T.{u} U) := D