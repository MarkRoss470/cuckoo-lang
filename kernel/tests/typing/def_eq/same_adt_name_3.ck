data T.{u} : Type where

data Dep : Type -> Prop where

def d1.{u} (D : Dep T.{u}) : Dep T.{u} := D -- Okay
def d1.{u, v} (D : Dep T.{u}) : Dep T.{v} := D -- Error
