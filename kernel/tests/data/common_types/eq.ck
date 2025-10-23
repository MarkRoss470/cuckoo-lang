data Eq.{u} (T : Sort u) (x : T) : T -> Prop where
  | refl : Eq T x x

def eq_rec.{u, m} :
    (T : Sort u)
    -> (x : T)
    -> (motive : (y : T) -> (Eq.{u} T x y) -> Sort m)
    -> (refl : motive x (Eq.refl.{u} T x))
    -> (y : T)
    -> (e : Eq.{u} T x y)
    -> motive y e
    := Eq.rec.{u, m}