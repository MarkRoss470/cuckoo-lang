-- A proposition which is trivially inhabited
data True : Prop where
  | intro : True

-- A proposition which is trivially uninhabited. Negation is expressed by using implication of False
-- because `¬P` is logically equivalent to `P -> False`
data False : Prop where

-- False implies anything
def False.elim.{u} (T : Sort u) (f : False) : T := False.rec.{u} (fun (_ : False) => T) f

-- Either a proof of A or a proof of B
data Or (A : Prop) (B : Prop) : Prop where
  | inl : A -> Or A B
  | inr : B -> Or A B

-- If `A -> C` and `B -> C`, then `Or A B -> C`
def Or.elim (A : Prop) (B : Prop) (C : Prop) (hac: A -> C) (hbc : B -> C) (h : Or A B) : C
    := Or.rec A B
        (fun (_ : Or A B) => C)
        (fun (ha : A) => hac ha)
        (fun (hb : B) => hbc hb)
        h

-- A proof of both A and B
data And (A : Prop) (B : Prop) : Prop where
  | mk : A -> B -> And A B

-- If `A -> B -> C`, then `And A B -> C`
def And.elim.{u} (A : Prop) (B : Prop) (C : Sort u) (hi : A -> B -> C) (ha : And A B) : C
    := And.rec.{u} A B
        (fun (_ : And A B) => C)
        (fun (a : A) (b : B) => hi a b)
        ha

-- A proof of equality between two values
data Eq.{u} (T : Sort u) (x : T) : T -> Prop where
  | refl : Eq T x x

-- x = y -> y = x
def Eq.symm.{u} (T : Sort u) (x : T) (y : T) (h : Eq.{u} T x y) : Eq.{u} T y x
    := Eq.rec.{u, 0} T x
        (fun (y : T) => fun (_ : Eq.{u} T x y) => Eq.{u} T y x)
        (Eq.refl.{u} T x)
        y
        h

-- x = y -> f x = f y
def Eq.cong.{u, v} (T : Sort u) (U : Sort v) (x : T) (y : T) (f : T -> U) (h : Eq.{u} T x y) : Eq.{v} U (f x) (f y)
    := Eq.rec.{u, 0} T x
        (fun (y : T) => fun (_ : Eq.{u} T x y) => Eq.{v} U (f x) (f y))
        (Eq.refl.{v} U (f x))
        y
        h

-- `x = y` and `y = z` implies `x = z`
def Eq.trans.{u} (T : Sort u) (x : T) (y : T) (z : T) (hxy : Eq.{u} T x y) (hyz : Eq.{u} T y z) : Eq.{u} T x z
    := Eq.rec.{u, 0} T y
        (fun (z : T) => fun (_ : Eq.{u} T y z) => Eq.{u} T x z)
        hxy
        z
        hyz

-- If `T = U`, then a value `x` of type `T` can be converted to have type `U`
def Eq.conv.{u} (T : Sort u) (U : Sort u) (h : Eq.{(succ u)} (Sort u) T U) (x : T) : U
    := Eq.rec.{(succ u), u} (Sort u) T
        (fun (U : Sort u) => fun (_ : Eq.{(succ u)} (Sort u) T U) => U)
        x
        U
        h

-- A proof that there exists a value which satisfies some predicate
data Exists.{u} (T : Sort u) (P : T -> Prop) : Prop where
  | mk : (x : T) -> P x -> Exists T P

-- Uses a function of type `(x : T) -> P x -> Q` to eliminate `Exists T P` to `Q`
def Exists.elim.{u} (T : Sort u)
        (P : T -> Prop) (Q : Prop)
        (hpq : (x : T) -> P x -> Q)
        (hex : Exists.{u} T P)
        : Q
    := Exists.rec.{u} T P (fun (_: Exists.{u} T P) => Q) hpq hex

-- Uses a function of type `(x : T) -> P x -> Q x` to eliminate `Exists T P` to `Exists T Q`
def Exists.elim_forall.{u} (T : Sort u)
        (P : T -> Prop) (Q : T -> Prop)
        (hpq : (x : T) -> P x -> Q x)
        (hex : Exists.{u} T P)
        : Exists.{u} T Q
    := Exists.elim.{u} T
        P (Exists.{u} T Q)
        (fun (x : T) (hp : P x) => Exists.mk.{u} T Q x (hpq x hp))
        hex

-- A proof of either P or ¬P. This is in `Type` rather than `Prop` so that it is not proof-irrelevant.
data Decidable (P : Prop) : Type where
  | is_true : P -> Decidable P
  | is_false : (P -> False) -> Decidable P

-- A type has decidable equality if `x = y` is decidable for any `x` and `y`
def DecidableEq.{u} (T : Sort u) : Sort (max u 1) := (x : T) -> (y : T) -> Decidable (Eq.{u} T x y)

-- All propositions have decidable equality because all proofs of a theorem are definitionally equal
def DecidableEq.decidable_eq_prop (P : Prop) : DecidableEq.{0} P
    := fun (x : P) (y : P) => Decidable.is_true (Eq.{0} P x y) (Eq.refl.{0} P x)