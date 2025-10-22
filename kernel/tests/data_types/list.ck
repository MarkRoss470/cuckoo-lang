data List.{u} (T : Type u) : Type u where
  | nil : List T
  | cons : T -> List T -> List T

def list_rec.{u, m} :
    (T : Type u)
    -> (motive : List.{u} T -> Sort m)
    -> (nil : motive (List.nil.{u} T))
    -> (cons : (x : T) -> (xs : List.{u} T) -> motive xs -> motive (List.cons.{u} T x xs))
    -> (l : List.{u} T)
    -> motive l
    := List.rec.{u, m}