data Unit : Type where
  | mk : Unit

data SomeTy.{u} (T : Sort u) : T -> Unit -> Prop where

def some_ty_rec.{u} (T : Sort u) (x : T) (h : SomeTy.{u} T x (Unit.mk)) : Unit := SomeTy.rec.{u, 1}
    T
    (fun (x : T) (u : Unit) (_ : SomeTy.{u} T x u) => Unit)
    x
    Unit.mk
    h