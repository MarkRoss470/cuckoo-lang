data Bool : Type where
  | true : Bool
  | false : Bool

def bool_rec.{m} :
    (motive : Bool -> Sort m)
    -> (true : motive Bool.true)
    -> (false : motive Bool.false)
    -> (b : Bool)
    -> motive b
    := Bool.rec.{m}