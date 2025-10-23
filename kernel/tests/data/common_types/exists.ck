data Exists.{u} (T : Sort u) (P : T -> Prop) : Prop where
  | mk : (x : T) -> (P x) -> Exists T P

def exists_rec.{u} :
    (T : Sort u)
    -> (P : T -> Prop)
    -> (motive : (Exists.{u} T P) -> Sort)
    -> (mk : (x : T) -> (h : P x) -> motive (Exists.mk.{u} T P x h))
    -> (h : Exists.{u} T P)
    -> motive h
    := Exists.rec.{u}