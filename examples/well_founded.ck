import nat.ck

-- The accessibility relation, which states there are no infinite descending chains of elements related by `R` which
-- end at the element `x`
data Acc.{u} (T : Sort u) (R : T -> T -> Prop) : T -> Prop where
  | acc : (x : T) -> ((y : T) -> R y x -> Acc T R y) -> Acc T R x

-- A relation is 'well-founded' if all elements of its domain are accessible. This means that the relation has no
-- infinite descending chains, so it can be used for recursion without introducing inconsistencies.
def WellFounded.{u} (T : Sort u) (R : T -> T -> Prop) : Prop := (x : T) -> Acc.{u} T R x

-- The well-founded fix-point operation. If a function can be defined using only recursive calls with an argument less
-- than its input as judged by a well-founded relation `R`, then the function is defined for all values in `T`
def WellFounded.fix.{u, v} (T : Sort u) (R : T -> T -> Prop)
        (C : T -> Sort v) (hwf : WellFounded.{u} T R)
        (F : (x : T) -> ((y : T) -> R y x -> C y) -> C x)
        (x : T)
        : C x
    := Acc.rec.{u, v} T R
        (fun (x : T) => fun (h : Acc.{u} T R x) => C x)
        (fun (x : T)
            => fun (hx : (y : T) -> R y x -> Acc.{u} T R y)
            => fun (hc : (y : T) -> (hy : R y x) -> C y)
            => F x hc)
        x (hwf x)

-- ------------------------------------------------------------------------------------------------------------
--                                               Well-foundedness lemmas
-- ------------------------------------------------------------------------------------------------------------

-- The empty relation is well-founded
def WellFounded.empty_relation_well_founded.{u} (T : Sort u)
        : WellFounded.{u} T (fun (_ : T) (_ : T) => False)
    := fun (x : T)
    => Acc.acc.{u} T (fun (_ : T) (_ : T) => False) x
        (fun (y : T) (hf : False) => False.elim.{0} (Acc.{u} T (fun (_ : T) (_ : T) => False) y) hf)

-- If a relation has an infinite descending chain, then it is not well-founded, where an infinite descending chain
-- is a function `f : Nat -> T` where `f (n + 1) < f n` for all `n`.
def WellFounded.no_infinite_descending_chain.{u} (T : Sort u) (R : T -> T -> Prop)
        (hwf : WellFounded.{u} T R) (f : Nat -> T) (hf : (n : Nat) -> R (f (Nat.succ n)) (f n))
        : False
    := WellFounded.fix.{u, 0} T R
        (fun (x : T) => (n : Nat) -> Eq.{u} T x (f n) -> False) hwf
        (fun (x : T)
            (hy : (y : T) -> R y x -> (n : Nat) -> Eq.{u} T y (f n) -> False)
            (n : Nat)
            (heq : Eq.{u} T x (f n))
            => hy
                (f (Nat.succ n))
                (Eq.conv.{0}
                    (R (f (Nat.succ n)) (f n))
                    (R (f (Nat.succ n)) x)
                    (Eq.cong.{u, 1} T Prop (f n) x (fun (x : T) => R (f (Nat.succ n)) x) (Eq.symm.{u} T x (f n) heq))
                    (hf n))
                (Nat.succ n)
                (Eq.refl.{u} T (f (Nat.succ n))))
        (f Nat.zero)
        Nat.zero
        (Eq.refl.{u} T (f Nat.zero))

-- Well-founded relations do not have fixed points
def WellFounded.no_fixed_point.{u} (T : Sort u) (R : T -> T -> Prop)
        (hwf : WellFounded.{u} T R)
        (x : T) (hx : R x x)
        : False
    := WellFounded.no_infinite_descending_chain.{u} T R hwf
        (fun (_ : Nat) => x)
        (fun (_ : Nat) => hx)

-- The equality relation on an inhabited type is not well-founded
def WellFounded.eq_not_well_founded.{u} (T : Sort u) (x : T) (hwf : WellFounded.{u} T (Eq.{u} T)) : False
    := WellFounded.no_fixed_point.{u} T (Eq.{u} T) hwf x (Eq.refl.{u} T x)

-- ------------------------------------------------------------------------------------------------------------
--                         Proof that less-than on natural numbers is well-founded
-- ------------------------------------------------------------------------------------------------------------

-- Zero is accessible under the less-than relation
def Nat.zero_acc_lt : Acc.{1} Nat Nat.Lt Nat.zero := Acc.acc.{1} Nat Nat.Lt Nat.zero
    (fun (y : Nat) (hy : Nat.Lt y Nat.zero) => False.elim.{0} (Acc.{1} Nat Nat.Lt y) (Nat.not_lt_zero y hy))

-- If x is accessible and y = x, then y is accessible
def Nat.conv_acc_lt (x : Nat) (y : Nat) (hx : Acc.{1} Nat Nat.Lt x) (heq : Eq.{1} Nat y x) : Acc.{1} Nat Nat.Lt y
    := Eq.conv.{0}
        (Acc.{1} Nat Nat.Lt x)
        (Acc.{1} Nat Nat.Lt y)
        (Eq.cong.{1, 1} Nat Prop x y (fun (x : Nat) => Acc.{1} Nat Nat.Lt x) (Eq.symm.{1} Nat y x heq))
        hx

-- If x is accessible and y < x, then y is accessible
def Nat.lt_acc (x : Nat) (y : Nat) (hx : Acc.{1} Nat Nat.Lt x) (hlt : Nat.Lt y x) : Acc.{1} Nat Nat.Lt y
    := Acc.rec.{1, 0} Nat Nat.Lt
        (fun (x' : Nat) (_ : Acc.{1} Nat Nat.Lt x') => Eq.{1} Nat x x' -> Acc.{1} Nat Nat.Lt y)
        (fun (x' : Nat)
            (h : (y' : Nat) -> Nat.Lt y' x' -> Acc.{1} Nat Nat.Lt y')
            (_ : (y' : Nat) -> Nat.Lt y' x' -> Eq.{1} Nat x y' -> Acc.{1} Nat Nat.Lt y)
            (heq : Eq.{1} Nat x x')
            => h y (Eq.conv.{0} (Nat.Lt y x) (Nat.Lt y x') (Eq.cong.{1, 1} Nat Prop x x' (fun (x : Nat) => Nat.Lt y x) heq) hlt))
        x hx
        (Eq.refl.{1} Nat x)

-- If x is accessible under the less-than relation, then so is x + 1
def Nat.succ_acc_lt (x : Nat) (hx : Acc.{1} Nat Nat.Lt x) : Acc.{1} Nat Nat.Lt (Nat.succ x)
    := Acc.acc.{1} Nat Nat.Lt (Nat.succ x)
        (fun (y : Nat)
         => fun (hy : Nat.Lt y (Nat.succ x))
         => Or.elim (Eq.{1} Nat y x) (Nat.Lt y x) (Acc.{1} Nat Nat.Lt y)
             (Nat.conv_acc_lt x y hx)
             (Nat.lt_acc x y hx)
             (Nat.le_dichotomy y x (Nat.succ_le_succ_mpr y x hy)))

-- The less-than relation on natural numbers is well founded
def Nat.Lt.well_founded : WellFounded.{1} Nat Nat.Lt
    := fun (x : Nat)
    => Nat.rec.{0}
        (fun (x : Nat) => Acc.{1} Nat Nat.Lt x)
        Nat.zero_acc_lt
        (fun (x : Nat) (hx : Acc.{1} Nat Nat.Lt x) => Nat.succ_acc_lt x hx)
        x
