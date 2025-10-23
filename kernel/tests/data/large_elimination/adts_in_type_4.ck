data Unit : Type where
  | mk : Unit

data SomeTy.{u} (T : Sort u) : Type u where
  | c : T -> SomeTy T

def some_ty_rec.{u} (T : Sort u) (x : SomeTy.{u} T) : Unit := SomeTy.rec.{u, 1}
    T
    (fun (_ : SomeTy.{u} T) => Unit)
    (fun (_ : T) => Unit.mk)
    x
