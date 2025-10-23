data Unit : Type where
  | mk : Unit

data SomeTy : Prop where

def some_ty_rec (h : SomeTy) : Unit := SomeTy.rec.{1}
    (fun (_ : SomeTy) => Unit)
    h