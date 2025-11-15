data Nat : Type where
  | zero : Nat
  | succ : Nat -> Nat

def zero : Nat := Nat.zero
def one : Nat := Nat.succ zero
def two : Nat := Nat.succ one
def three : Nat := Nat.succ two
def four : Nat := Nat.succ three
def five : Nat := Nat.succ four
def six : Nat := Nat.succ five
def seven : Nat := Nat.succ six
def eight : Nat := Nat.succ seven

-- Addition of natural numbers
def add (m : Nat) (n : Nat) : Nat := Nat.rec.{1}
    (fun (m : Nat) => Nat)
    n                                                    -- If m = 0, m + n = n
    (fun (_ : Nat) => fun (x : Nat) => Nat.succ x)       -- If m = succ m' and m' + n = x, then m + n = succ x
    m

data Dep : Nat -> Type where

def zero_plus_zero (D : Dep (add zero zero)) : Dep zero := D
def zero_plus_one (D : Dep (add zero one)) : Dep one := D
def two_plus_two (D : Dep (add two two)) : Dep four := D
def two_plus_five (D : Dep (add two five)) : Dep seven := D
def five_plus_two_eq_two_plus_five (D : Dep (add five two)) : Dep (add two five) := D
def eight_plus_zero_eq_five_plus_three (D : Dep (add eight zero)) : Dep (add five three) := D