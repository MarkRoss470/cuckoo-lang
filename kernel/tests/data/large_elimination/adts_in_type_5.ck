data Unit : Type where
  | mk : Unit

data SomeTy.{u} (T : Sort u) : Unit -> Type u where
  | c : T -> SomeTy T Unit.mk
  | d : SomeTy T Unit.mk

def some_ty_rec.{u} (T : Sort u) (x : SomeTy.{u} T Unit.mk) : Unit := SomeTy.rec.{u, 1}
    T
    (fun (u : Unit) (_ : SomeTy.{u} T u) => Unit)
    (fun (_ : T) => Unit.mk)
    Unit.mk
    Unit.mk
    x
