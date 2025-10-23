data Unit : Type where
  | mk : Unit

data SomeTy : Type where

def some_ty_rec (x : SomeTy) : Unit := SomeTy.rec.{1}
    (fun (_ : SomeTy) => Unit)
    x