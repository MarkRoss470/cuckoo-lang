data Nat : Type where
  | zero : Nat
  | succ : Nat -> Nat

def Nat.add (m : Nat) (n : Nat) : Nat := Nat.rec.{1}
    (fun (m : Nat) => Nat)
    n                                                    -- If m = 0, m + n = n
    (fun (_ : Nat) => fun (x : Nat) => Nat.succ x)       -- If m = succ m' and m' + n = x, then m + n = succ x
    m

data Vec.{u} (T : Type u) : Nat -> Type u where
  | nil : Vec T Nat.zero
  | cons : (n : Nat) -> T -> Vec T n -> Vec T (Nat.succ n)

-- These types are propositionally equal but not definitionally equal
def a (m : Nat) (n : Nat) (f : Vec.{0} Nat (Nat.add m n) -> Nat) (v : Vec.{0} Nat (Nat.add n m)) : Nat := f v