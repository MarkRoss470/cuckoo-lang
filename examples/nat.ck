import props.ck

-- The natural numbers starting from zero
data Nat : Type where
  | zero : Nat
  | succ : Nat -> Nat

-- A non-recursive eliminator for `Nat`
def Nat.casesOn.{u} (motive : Nat -> Sort u) (n : Nat) (zero : motive Nat.zero) (succ : (n : Nat) -> motive (Nat.succ n)) : motive n
    := Nat.rec.{u} motive zero (fun (n : Nat) => fun (_ : motive n) => succ n) n

-- A type which makes it easy to reason about whether two values of type `Nat` are equal.
-- This type is logically equivalent to `True` if `x1 = x2`, and equivalent to `P` otherwise.
def Nat.noConfusionType.{u} (P : Sort u) (x1 : Nat) (x2 : Nat) : Sort u
    := Nat.casesOn.{(succ u)} (fun (_ : Nat) => Sort u) x1
        (Nat.casesOn.{(succ u)} (fun (_ : Nat) => Sort u) x2 (P -> P) (fun (_ : Nat) => P))
        (fun (n : Nat) => Nat.casesOn.{(succ u)} (fun (_ : Nat) => Sort u) x2 P (fun (n' : Nat) => (Eq.{1} Nat n n' -> P) -> P))

def Nat.one : Nat := Nat.succ Nat.zero
def Nat.two : Nat := Nat.succ Nat.one
def Nat.three : Nat := Nat.succ Nat.two
def Nat.four : Nat := Nat.succ Nat.three

-- Addition of natural numbers
def Nat.add (m : Nat) (n : Nat) : Nat := Nat.rec.{1}
    (fun (m : Nat) => Nat)
    n                                                    -- If m = 0, m + n = n
    (fun (_ : Nat) => fun (x : Nat) => Nat.succ x)       -- If m = succ m' and m' + n = x, then m + n = succ x
    m

-- Multiplication of natural numbers
def Nat.mul (m : Nat) (n : Nat) : Nat := Nat.rec.{1}
    (fun (m : Nat) => Nat)
    Nat.zero                                             -- If m = 0, m * n = 0
    (fun (_ : Nat) => fun (x : Nat) => Nat.add n x)      -- If m = succ m' and m' * n = x, then m * n = n + x
    m

-- A proposition asserting that n is zero
def Nat.IsZero (n : Nat) : Prop := Nat.casesOn.{1} (fun (_ : Nat) => Prop) n True (fun (_ : Nat) => False)

-- A proposition asserting that n is zero or one
def Nat.LeOne (n : Nat) : Prop := Nat.casesOn.{1} (fun (_ : Nat) => Prop) n True (fun (n : Nat) => Nat.IsZero n)

-- 0 != succ n
def Nat.zero_ne_succ (n : Nat) (h : Eq.{1} Nat Nat.zero (Nat.succ n)) : False := Eq.rec.{1, 0}
    Nat
    Nat.zero
    (fun (x : Nat) => fun (hx : Eq.{1} Nat Nat.zero x) => Nat.IsZero x)
    True.intro
    (Nat.succ n)
    h

-- 1 != succ (succ n)
def Nat.one_ne_succ_succ (n : Nat) (h : Eq.{1} Nat Nat.one (Nat.succ (Nat.succ n))) : False := Eq.rec.{1, 0}
    Nat
    Nat.one
    (fun (x : Nat) => fun (hx : Eq.{1} Nat Nat.one x) => Nat.LeOne x)
    True.intro
    (Nat.succ (Nat.succ n))
    h

-- succ a = succ b -> a = b
def Nat.succ_inj (a : Nat) (b : Nat) (h : Eq.{1} Nat (Nat.succ a) (Nat.succ b)) : Eq.{1} Nat a b
    := Eq.rec.{1, 0} Nat (Nat.succ a)
        (fun (n : Nat) => fun (_ : Eq.{1} Nat (Nat.succ a) n) => Nat.noConfusionType.{0} (Eq.{1} Nat a b) (Nat.succ a) n)
        (fun (h: Eq.{1} Nat a a -> Eq.{1} Nat a b) => h (Eq.refl.{1} Nat a))
        (Nat.succ b)
        h
        (fun (hab: Eq.{1} Nat a b) => hab)

-- n != succ n
def Nat.n_ne_succ_n (n : Nat) (heq : Eq.{1} Nat n (Nat.succ n)) : False := Nat.rec.{0}
    (fun (n : Nat) => Eq.{1} Nat n (Nat.succ n) -> False)
    (Nat.zero_ne_succ Nat.zero)
    (fun (n : Nat)
        (hneq : (Eq.{1} Nat n (Nat.succ n)) -> False)
        (heq : Eq.{1} Nat (Nat.succ n) (Nat.succ (Nat.succ n)))
        => hneq (Nat.succ_inj n (Nat.succ n) heq))
    n heq

-- m = n -> f(m) = f(n)
def Nat.cong (m : Nat) (n : Nat) (f : Nat -> Nat) (h : Eq.{1} Nat m n) : Eq.{1} Nat (f m) (f n) :=
    Eq.cong.{1, 1} Nat Nat m n f h

-- n + 0 = n
def Nat.add_zero (n : Nat) : Eq.{1} Nat (Nat.add n Nat.zero) n
    := Nat.rec.{0}
        (fun (x : Nat) => Eq.{1} Nat (Nat.add x Nat.zero) x)
        (Eq.refl.{1} Nat Nat.zero)
        (fun (x : Nat) => fun (hx : Eq.{1} Nat (Nat.add x Nat.zero) x) => Nat.cong (Nat.add x Nat.zero) x Nat.succ hx)
        n

-- m + succ n = succ (m + n)
def Nat.add_succ (m : Nat) (n : Nat) : Eq.{1} Nat (Nat.add m (Nat.succ n)) (Nat.succ (Nat.add m n))
    := Nat.rec.{0}
        (fun (m : Nat) => Eq.{1} Nat (Nat.add m (Nat.succ n)) (Nat.succ (Nat.add m n)))
        (Eq.refl.{1} Nat (Nat.succ n))
        (fun (m : Nat)
            => fun (h : Eq.{1} Nat (Nat.add m (Nat.succ n)) (Nat.succ (Nat.add m n)))
            => Nat.cong (Nat.add m (Nat.succ n)) (Nat.succ (Nat.add m n)) Nat.succ h)
        m

-- m + n = n + m
def Nat.add_comm (m : Nat) (n : Nat) : Eq.{1} Nat (Nat.add m n) (Nat.add n m)
    := Nat.rec.{0}
    (fun (m : Nat) => Eq.{1} Nat (Nat.add m n) (Nat.add n m))
    (Eq.symm.{1} Nat (Nat.add n Nat.zero) n (Nat.add_zero n))
    (fun (m : Nat)
        => fun (h : Eq.{1} Nat (Nat.add m n) (Nat.add n m))
        => Eq.trans.{1} Nat (Nat.succ (Nat.add m n)) (Nat.succ (Nat.add n m)) (Nat.add n (Nat.succ m))
            (Nat.cong (Nat.add m n) (Nat.add n m) Nat.succ h)
            (Eq.symm.{1} Nat (Nat.add n (Nat.succ m)) (Nat.succ (Nat.add n m)) (Nat.add_succ n m)))
    m

-- (a + b) + c = a + (b + c)
def Nat.add_assoc (a : Nat) (b : Nat) (c : Nat)
        : Eq.{1} Nat (Nat.add (Nat.add a b) c) (Nat.add a (Nat.add b c))
    := Nat.rec.{0}
        (fun (a : Nat) => Eq.{1} Nat (Nat.add (Nat.add a b) c) (Nat.add a (Nat.add b c)))
        (Eq.refl.{1} Nat (Nat.add b c))
        (fun (a : Nat) (h : Eq.{1} Nat (Nat.add (Nat.add a b) c) (Nat.add a (Nat.add b c)))
            => Nat.cong ((Nat.add (Nat.add a b) c)) (Nat.add a (Nat.add b c)) Nat.succ h)
        a

-- a + (b + c) = b + (a + c)
def Nat.add_abc_bac (a : Nat) (b : Nat) (c : Nat) : Eq.{1} Nat (Nat.add a (Nat.add b c)) (Nat.add b (Nat.add a c))
    := Eq.trans.{1} Nat
        (Nat.add a (Nat.add b c)) -- a + (b + c)
        (Nat.add (Nat.add a b) c) -- (a + b) + c
        (Nat.add b (Nat.add a c)) -- b + (a + c)
        (Eq.symm.{1} Nat (Nat.add (Nat.add a b) c) (Nat.add a (Nat.add b c)) (Nat.add_assoc a b c))
        (Eq.trans.{1} Nat
            (Nat.add (Nat.add a b) c) -- (a + b) + c
            (Nat.add (Nat.add b a) c) -- (b + a) + c
            (Nat.add b (Nat.add a c)) -- b + (a + c)
            (Nat.cong (Nat.add a b) (Nat.add b a) (fun (s : Nat) => Nat.add s c) (Nat.add_comm a b))
            (Nat.add_assoc b a c)
        )

-- (a + b) + (c + d) = (a + c) + (b + d)
def Nat.add_abcd_acbd (a : Nat) (b : Nat) (c : Nat) (d : Nat)
        : Eq.{1} Nat (Nat.add (Nat.add a b) (Nat.add c d)) (Nat.add (Nat.add a c) (Nat.add b d))
    := Eq.trans.{1} Nat
        (Nat.add (Nat.add a b) (Nat.add c d)) -- (a + b) + (c + d)
        (Nat.add a (Nat.add b (Nat.add c d))) -- a + (b + (c + d))
        (Nat.add (Nat.add a c) (Nat.add b d)) -- (a + c) + (b + d)
        (Nat.add_assoc a b (Nat.add c d))
        (Eq.trans.{1} Nat
            (Nat.add a (Nat.add b (Nat.add c d))) -- a + (b + (c + d))
            (Nat.add a (Nat.add (Nat.add c d) b)) -- a + ((c + d) + b)
            (Nat.add (Nat.add a c) (Nat.add b d)) -- (a + c) + (b + d)
            (Nat.cong (Nat.add b (Nat.add c d)) (Nat.add (Nat.add c d) b) (Nat.add a)
                (Nat.add_comm b (Nat.add c d)))
            (Eq.trans.{1} Nat
                (Nat.add a (Nat.add (Nat.add c d) b)) -- a + ((c + d) + b)
                (Nat.add a (Nat.add c (Nat.add d b))) -- a + (c + (d + b))
                (Nat.add (Nat.add a c) (Nat.add b d)) -- (a + c) + (b + d)
                (Nat.cong (Nat.add (Nat.add c d) b) (Nat.add c (Nat.add d b)) (Nat.add a)
                    (Nat.add_assoc c d b))
                (Eq.trans.{1} Nat
                    (Nat.add a (Nat.add c (Nat.add d b))) -- a + (c + (d + b))
                    (Nat.add (Nat.add a c) (Nat.add d b)) -- (a + c) + (d + b)
                    (Nat.add (Nat.add a c) (Nat.add b d)) -- (a + c) + (b + d)
                    (Eq.symm.{1} Nat
                        (Nat.add (Nat.add a c) (Nat.add d b))
                        (Nat.add a (Nat.add c (Nat.add d b)))
                        (Nat.add_assoc a c (Nat.add d b)))
                    (Nat.cong (Nat.add d b) (Nat.add b d) (Nat.add (Nat.add a c)) (Nat.add_comm d b))
                )
            )
        )

-- n * 0 = 0
def Nat.mul_zero (n : Nat) : Eq.{1} Nat (Nat.mul n Nat.zero) Nat.zero
    := Nat.rec.{0}
        (fun (n : Nat) => Eq.{1} Nat (Nat.mul n Nat.zero) Nat.zero)
        (Eq.refl.{1} Nat Nat.zero)
        (fun (n : Nat) (h : Eq.{1} Nat (Nat.mul n Nat.zero) Nat.zero) => h)
        n

-- 1 * n = n
def Nat.one_mul (n : Nat) : Eq.{1} Nat (Nat.mul Nat.one n) n := Nat.add_zero n

-- n * 1 = n
def Nat.mul_one (n : Nat) : Eq.{1} Nat (Nat.mul n Nat.one) n
    := Nat.rec.{0}
        (fun (n : Nat) => Eq.{1} Nat (Nat.mul n Nat.one) n)
        (Eq.refl.{1} Nat Nat.zero)
        (fun (n : Nat) (h : Eq.{1} Nat (Nat.mul n Nat.one) n)
            => Nat.cong (Nat.mul n Nat.one) n Nat.succ h)
        n



-- m * succ n = m + m * n
def Nat.mul_succ (m : Nat) (n : Nat) : Eq.{1} Nat (Nat.mul m (Nat.succ n)) (Nat.add m (Nat.mul m n))
    := Nat.rec.{0}
        (fun (m : Nat) => Eq.{1} Nat (Nat.mul m (Nat.succ n)) (Nat.add m (Nat.mul m n)))
        (Eq.refl.{1} Nat Nat.zero)
        (fun (m : Nat) (h : Eq.{1} Nat (Nat.mul m (Nat.succ n)) (Nat.add m (Nat.mul m n)))
            => Nat.cong
                (Nat.add n (Nat.mul m (Nat.succ n))) -- (succ m) * (succ n) = succ (n + m * succ n)
                (Nat.add m (Nat.add n (Nat.mul m n)))
                Nat.succ
                (Eq.trans.{1} Nat
                    (Nat.add n (Nat.mul m (Nat.succ n)))
                    (Nat.add n (Nat.add m (Nat.mul m n)))
                    (Nat.add m (Nat.add n (Nat.mul m n)))
                    (Nat.cong (Nat.mul m (Nat.succ n)) (Nat.add m (Nat.mul m n)) (Nat.add n) h)
                    (Nat.add_abc_bac n m (Nat.mul m n))
                )
        )
        m

-- m * n = n * m
def Nat.mul_comm (m : Nat) (n : Nat) : Eq.{1} Nat (Nat.mul m n) (Nat.mul n m)
    := Nat.rec.{0}
        (fun (m : Nat) => Eq.{1} Nat (Nat.mul m n) (Nat.mul n m))
        (Eq.symm.{1} Nat (Nat.mul n Nat.zero) Nat.zero (Nat.mul_zero n))
        (fun (m : Nat) (h : Eq.{1} Nat (Nat.mul m n) (Nat.mul n m))
            => Eq.trans.{1} Nat
                (Nat.add n (Nat.mul m n)) -- succ m * n = n + m * n
                (Nat.add n (Nat.mul n m)) -- n + n * m
                (Nat.mul n (Nat.succ m))  -- n * succ m
                (Nat.cong (Nat.mul m n) (Nat.mul n m) (Nat.add n) h)
                (Eq.symm.{1} Nat (Nat.mul n (Nat.succ m)) (Nat.add n (Nat.mul n m))
                    (Nat.mul_succ n m))
            )
        m

-- a * (b + c) = (a * b) + (a * c)
def Nat.mul_add_r (a : Nat) (b : Nat) (c : Nat)
        : Eq.{1} Nat (Nat.mul a (Nat.add b c)) (Nat.add (Nat.mul a b) (Nat.mul a c))
    := Nat.rec.{0}
        (fun (a : Nat) => Eq.{1} Nat (Nat.mul a (Nat.add b c)) (Nat.add (Nat.mul a b) (Nat.mul a c)))
        (Eq.refl.{1} Nat Nat.zero)
        (fun (a : Nat) (h : Eq.{1} Nat (Nat.mul a (Nat.add b c)) (Nat.add (Nat.mul a b) (Nat.mul a c)))
            => Eq.trans.{1} Nat
                (Nat.add (Nat.add b c) (Nat.mul a (Nat.add b c)))              -- (succ a) * (b + c) = (b + c) + a * (b + c)
                (Nat.add (Nat.add b c) (Nat.add (Nat.mul a b) (Nat.mul a c)))  -- (b + c) + (a * b + a * c)
                (Nat.add (Nat.add b (Nat.mul a b)) (Nat.add c (Nat.mul a c)))  -- (b + a * b) + (c + a * c) = (succ a) * b + (succ a) * c
                (Nat.cong (Nat.mul a (Nat.add b c)) (Nat.add (Nat.mul a b) (Nat.mul a c)) (Nat.add (Nat.add b c)) h)
                (Nat.add_abcd_acbd b c (Nat.mul a b) (Nat.mul a c))
            )
        a

-- (a + b) * c = a * c + b * c
def Nat.mul_add_l (a : Nat) (b : Nat) (c : Nat)
        : Eq.{1} Nat (Nat.mul (Nat.add a b) c) (Nat.add (Nat.mul a c) (Nat.mul b c))
    := Eq.trans.{1} Nat
        (Nat.mul (Nat.add a b) c) -- (a + b) * c
        (Nat.mul c (Nat.add a b)) -- c * (a + b)
        (Nat.add (Nat.mul a c) (Nat.mul b c)) -- a * c + b * c
        (Nat.mul_comm (Nat.add a b) c)
        (Eq.trans.{1} Nat
            (Nat.mul c (Nat.add a b)) -- c * (a + b)
            (Nat.add (Nat.mul c a) (Nat.mul c b)) -- c * a + c * b
            (Nat.add (Nat.mul a c) (Nat.mul b c)) -- a * c + b * c
            (Nat.mul_add_r c a b)
            (Eq.trans.{1} Nat
                (Nat.add (Nat.mul c a) (Nat.mul c b)) -- c * a + c * b
                (Nat.add (Nat.mul c a) (Nat.mul b c)) -- c * a + b * c
                (Nat.add (Nat.mul a c) (Nat.mul b c)) -- a * c + b * c
                (Nat.cong (Nat.mul c b) (Nat.mul b c) (Nat.add (Nat.mul c a)) (Nat.mul_comm c b))
                (Nat.cong (Nat.mul c a) (Nat.mul a c) (fun (s : Nat) => (Nat.add s (Nat.mul b c))) (Nat.mul_comm c a))
            )
        )

-- (a * b) * c = a * (b * c)
def Nat.mul_assoc (a : Nat) (b : Nat) (c : Nat)
        : Eq.{1} Nat (Nat.mul (Nat.mul a b) c) (Nat.mul a (Nat.mul b c))
    := Nat.rec.{0}
       (fun (a : Nat) => Eq.{1} Nat (Nat.mul (Nat.mul a b) c) (Nat.mul a (Nat.mul b c)))
       (Eq.refl.{1} Nat Nat.zero)
       (fun (a : Nat) (h : Eq.{1} Nat (Nat.mul (Nat.mul a b) c) (Nat.mul a (Nat.mul b c)))
            => Eq.trans.{1} Nat
                (Nat.mul (Nat.add b (Nat.mul a b)) c)             -- ((succ a) * b) * c = (b + a * b) * c
                (Nat.add (Nat.mul b c) (Nat.mul (Nat.mul a b) c)) -- (b * c) + ((a * b) * c)
                (Nat.add (Nat.mul b c) (Nat.mul a (Nat.mul b c))) -- (b * c) + (a * (b * c)) = (succ a) * (b * c)
                (Nat.mul_add_l b (Nat.mul a b) c)
                (Nat.cong (Nat.mul (Nat.mul a b) c) (Nat.mul a (Nat.mul b c)) (Nat.add (Nat.mul b c)) h)
       )
       a

-- The less-than-or-equal relation on natural numbers
data Nat.Le (m : Nat) : Nat -> Prop where
  | refl : Le m m
  | step : (n : Nat) -> Le m n -> Le m (Nat.succ n)

-- The less-than relation on natural numbers
def Nat.Lt (m : Nat) (n : Nat) : Prop := Nat.Le (Nat.succ m) n

-- `m < n` implies `succ m < succ n`
def Nat.Lt.step (m : Nat) (n : Nat) (hmn : Nat.Lt m n) : Nat.Lt m (Nat.succ n)
    := Nat.Le.step (Nat.succ m) n hmn

-- ¬m < 0
def Nat.not_lt_zero (m : Nat) (hm : Nat.Lt m Nat.zero) : False
    := Nat.Le.rec (Nat.succ m)
        (fun (n : Nat) => fun (hm : Nat.Le (Nat.succ m) n) => (Eq.{1} Nat n Nat.zero) -> False)
        (fun (hm : Eq.{1} Nat (Nat.succ m) Nat.zero) => Nat.zero_ne_succ m (Eq.symm.{1} Nat (Nat.succ m) Nat.zero hm))
        (fun (n : Nat)
            => fun (_ : Nat.Le (Nat.succ m) n)
            => fun (_: Eq.{1} Nat n Nat.zero -> False)
            => fun (hn : Eq.{1} Nat (Nat.succ n) Nat.zero)
            => Nat.zero_ne_succ n (Eq.symm.{1} Nat (Nat.succ n) Nat.zero hn))
        Nat.zero
        hm
        (Eq.refl.{1} Nat Nat.zero)

-- m <= n -> succ m <= succ n
def Nat.succ_le_succ_mp (m : Nat) (n : Nat) (h : Nat.Le m n) : Nat.Le (Nat.succ m) (Nat.succ n)
    := Nat.Le.rec m
        (fun (n : Nat) => fun (_ : Nat.Le m n) => Nat.Le (Nat.succ m) (Nat.succ n))
        (Nat.Le.refl (Nat.succ m))
        (fun (n : Nat)
            => fun (_ : Nat.Le m n)
            => fun (h : Nat.Le (Nat.succ m) (Nat.succ n))
            => Nat.Le.step (Nat.succ m) (Nat.succ n) h)
        n
        h

-- succ m <= succ n -> m <= n
def Nat.succ_le_succ_mpr (m : Nat) (n : Nat) (h : Nat.Le (Nat.succ m) (Nat.succ n)) : Nat.Le m n
    := Nat.Le.rec (Nat.succ m)
        (fun (n : Nat) => fun (_ : Nat.Le (Nat.succ m) n) => (n' : Nat) -> Eq.{1} Nat n (Nat.succ n') -> Nat.Le m n')
        (fun (n' : Nat)
            => fun (heq : Eq.{1} Nat (Nat.succ m) (Nat.succ n'))
            => Eq.conv.{0} (Nat.Le m m) (Nat.Le m n')
                (Eq.cong.{1, 1} Nat Prop m n' (fun (n : Nat) => Nat.Le m n) (Nat.succ_inj m n' heq))
                (Nat.Le.refl m))
        (fun (n : Nat)
            => fun (hle : Nat.Le (Nat.succ m) n)
            => fun (h : (n' : Nat) -> Eq.{1} Nat n (Nat.succ n') -> Nat.Le m n')
            => fun (n' : Nat)
            => fun (heq : Eq.{1} Nat (Nat.succ n) (Nat.succ n'))
            => Nat.rec.{0}
                (fun (n' : Nat) => Eq.{1} Nat n n' -> Nat.Le m n')
                (fun (h : Eq.{1} Nat n Nat.zero) => False.elim.{0} (Nat.Le m Nat.zero)
                    (Nat.not_lt_zero m
                        (Eq.conv.{0} (Nat.Le (Nat.succ m) n) (Nat.Le (Nat.succ m) Nat.zero)
                        (Eq.cong.{1, 1} Nat Prop n Nat.zero (fun (n : Nat) => Nat.Le (Nat.succ m) n) h) hle)))
                (fun (n' : Nat)
                    => fun (_ : Eq.{1} Nat n n' -> Nat.Le m n')
                    => fun (hn' : Eq.{1} Nat n (Nat.succ n'))
                    => Nat.Le.step m n' (h n' hn'))
                n' (Nat.succ_inj n n' heq))
        (Nat.succ n) h n (Eq.refl.{1} Nat (Nat.succ n))

-- m <= n -> m = n or m < n
def Nat.le_dichotomy (m : Nat) (n : Nat) (h : Nat.Le m n) : Or (Eq.{1} Nat m n) (Nat.Lt m n)
    := Nat.Le.rec m
        (fun (n : Nat) => fun (_: Nat.Le m n) => Or (Eq.{1} Nat m n) (Nat.Lt m n))
        (Or.inl (Eq.{1} Nat m m) (Nat.Lt m m) (Eq.refl.{1} Nat m))
        (fun (n : Nat)
            => fun (hn : Nat.Le m n)
            => fun (_ : Or (Eq.{1} Nat m n) (Nat.Lt m n))
            => Or.inr (Eq.{1} Nat m (Nat.succ n)) (Nat.Lt m (Nat.succ n)) (Nat.succ_le_succ_mp m n hn))
        n
        h

-- Nat.Le is transitive - a <= b -> b <= c -> a <= c
def Nat.le_trans (a : Nat) (b : Nat) (c : Nat) (hab : Nat.Le a b) (hbc : Nat.Le b c) : Nat.Le a c
    := Nat.Le.rec b
        (fun (c : Nat) (hbc : Nat.Le b c) => Nat.Le a c)
        hab
        (fun (c : Nat) (hbc : Nat.Le b c) (hac : Nat.Le a c) => Nat.Le.step a c hac)
        c hbc

-- Equality with zero is decidable
def Nat.decide_eq_zero (y : Nat) : Decidable (Eq.{1} Nat Nat.zero y) := Nat.casesOn.{1}
    (fun (y : Nat) => Decidable (Eq.{1} Nat Nat.zero y))
    y
    (Decidable.is_true (Eq.{1} Nat Nat.zero Nat.zero) (Eq.refl.{1} Nat Nat.zero))
    (fun (y' : Nat) => Decidable.is_false (Eq.{1} Nat Nat.zero (Nat.succ y')) (Nat.zero_ne_succ y'))

-- If x = y is decidable, then so is x + 1 = y + 1
def Nat.decide_eq_succ_succ (x : Nat) (y : Nat) (h : Decidable (Eq.{1} Nat x y))
        : Decidable (Eq.{1} Nat (Nat.succ x) (Nat.succ y))
    := Decidable.rec.{1} (Eq.{1} Nat x y)
        (fun (_ : Decidable (Eq.{1} Nat x y)) => Decidable (Eq.{1} Nat (Nat.succ x) (Nat.succ y)))
        (fun (heq : Eq.{1} Nat x y)
            => Decidable.is_true (Eq.{1} Nat (Nat.succ x) (Nat.succ y)) (Nat.cong x y Nat.succ heq))
        (fun (hneq : Eq.{1} Nat x y -> False)
            => Decidable.is_false (Eq.{1} Nat (Nat.succ x) (Nat.succ y))
            (fun (heq : Eq.{1} Nat (Nat.succ x) (Nat.succ y))
                => hneq (Nat.succ_inj x y heq)))
        h

-- If x = y is decidable, then so is x + 1 = y
def Nat.decide_eq_succ (x : Nat) (hdec : (y : Nat) -> Decidable (Eq.{1} Nat x y)) (y : Nat)
        : Decidable (Eq.{1} Nat (Nat.succ x) y)
    := Nat.casesOn.{1}
        (fun (y : Nat) => Decidable (Eq.{1} Nat (Nat.succ x) y)) y
        (Decidable.is_false (Eq.{1} Nat (Nat.succ x) Nat.zero)
            (fun (h : Eq.{1} Nat (Nat.succ x) Nat.zero) => Nat.zero_ne_succ x (Eq.symm.{1} Nat (Nat.succ x) Nat.zero h)))
        (fun (y' : Nat) => Nat.decide_eq_succ_succ x y' (hdec y'))

def Nat.decide_eq (x : Nat) (y : Nat) : Decidable (Eq.{1} Nat x y) := Nat.rec.{1}
    (fun (x : Nat) => (y : Nat) -> Decidable (Eq.{1} Nat x y))
    Nat.decide_eq_zero
    (fun (x : Nat) (hdec : (y : Nat) -> Decidable (Eq.{1} Nat x y)) (y : Nat) => Nat.decide_eq_succ x hdec y)
    x y

-- Equality on natural numbers is decidable
def Nat.decidable_eq : DecidableEq.{1} Nat := Nat.decide_eq