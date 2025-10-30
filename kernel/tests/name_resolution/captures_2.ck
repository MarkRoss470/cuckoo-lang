data Nat : Type where
  | zero : Nat
  | succ : Nat -> Nat

data Fin : Nat -> Type where
  | zero : (n : Nat) -> Fin n
  | succ : (n : Nat) -> Fin n -> Fin (Nat.succ n)

def t1 (f : Nat -> Nat) : Type := (fun (f : Nat -> Type) (x : Nat) => f x) Fin (f Nat.zero)
def t2 (f : Nat -> Nat) : t1 f := Fin.zero (f Nat.zero)