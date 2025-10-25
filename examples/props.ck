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
