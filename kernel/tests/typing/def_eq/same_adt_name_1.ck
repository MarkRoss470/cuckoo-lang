data T : Type where

data Dep : Type -> Prop where

def d1 (D : Dep T) : Dep T := D