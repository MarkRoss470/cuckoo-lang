data Nat : Type where
  | zero : Nat
  | succ : Nat -> Nat

data Vec.{u} (T : Type u) : Nat -> Type u where
  | nil : Vec T Nat.zero
  | cons : (n : Nat) -> T -> Vec T n -> Vec T (Nat.succ n)

def vec_rec.{u, m} :
    (T : Type u)
    -> (motive : (n : Nat) -> Vec.{u} T n -> Sort m)
    -> (nil : motive Nat.zero (Vec.nil.{u} T))
    -> (cons : (n : Nat)
        -> (x : T)
        -> (xs : Vec.{u} T n)
        -> (_ : motive n xs)
        -> motive (Nat.succ n) (Vec.cons.{u} T n x xs))
    -> (n : Nat)
    -> (v : Vec.{u} T n)
    -> motive n v
    := Vec.rec.{u, m}