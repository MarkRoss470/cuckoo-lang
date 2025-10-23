data Unit : Type where
  | mk : Unit

data SomeTy.{u} (T : Sort u) : Prop where

def some_ty_rec.{u} (T : Sort u) (h : SomeTy.{u} T) : Unit := SomeTy.rec.{u, 1}
    T
    (fun (_ : SomeTy.{u} T) => Unit)
    h