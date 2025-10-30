data Nat : Type where
  | zero : Nat
  | succ : Nat -> Nat

-- Use an axiom to prevent reduction
axiom someFun (n : Nat) (m : Nat) : Nat

def t (x : Nat) (y : Nat) : Nat := (fun (x : Nat) (y : Nat) => someFun x y) y