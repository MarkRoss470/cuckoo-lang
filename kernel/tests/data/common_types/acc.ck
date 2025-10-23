data Acc.{u} (T : Sort u) (R : T -> T -> Prop) : T -> Prop where
  | acc : (x : T) -> ((y : T) -> R y x -> Acc T R y) -> Acc T R x

def acc_rec.{u, m} :
    (T : Sort u)
    -> (R : T -> T -> Prop)
    -> (motive : (x : T) -> Acc.{u} T R x -> Sort m)
    -> (acc :
      (x : T)
      -> (h : (y : T) -> (R y x) -> Acc.{u} T R y)
      -> ((y : T) -> (hy : R y x) -> motive y (h y hy))
      -> motive x (Acc.acc.{u} T R x h))
    -> (x : T)
    -> (a : Acc.{u} T R x)
    -> motive x a
    := Acc.rec.{u, m}