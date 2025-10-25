import nat.ck

-- A list of values of type `T`
data List.{u} (T : Type u) : Type u where
  | nil : List T
  | cons : T -> List T -> List T

-- Maps each element using `f`
def List.map.{u, v} (T : Type u) (U : Type v) (f : T -> U) (l : List.{u} T) : List.{v} U
    := List.rec.{u, (succ v)} T
        (fun (_ : List.{u} T) => List.{v} U)
        (List.nil.{v} U)
        (fun (x : T) => fun (_ : List.{u} T) => fun (m : List.{v} U) => List.cons.{v} U (f x) m)
        l

-- Appends one list to another
def List.append.{u} (T : Type u) (l : List.{u} T) (r : List.{u} T) : List.{u} T
    := List.rec.{u, (succ u)} T
        (fun (_ : List.{u} T) => List.{u} T)
        r
        (fun (x : T) => fun (_ : List.{u} T) => fun (m : List.{u} T) => List.cons.{u} T x m)
        l

-- Calculates the length of a list
def List.length.{u} (T : Type u) (l : List.{u} T) : Nat
    := List.rec.{u, 1} T
        (fun (_ : List.{u} T) => Nat)
        Nat.zero
        (fun (_ : T) => fun (_ : List.{u} T) => fun (m : Nat) => Nat.succ m)
        l

-- l ++ [] = l
def List.append_nil.{u} (T : Type u) (l : List.{u} T)
        : Eq.{(succ u)} (List.{u} T) (List.append.{u} T l (List.nil.{u} T)) l
    := List.rec.{u, 0} T
        (fun (l : List.{u} T) => Eq.{(succ u)} (List.{u} T) (List.append.{u} T l (List.nil.{u} T)) l)
        (Eq.refl.{(succ u)} (List.{u} T) (List.nil.{u} T))
        (fun (x : T)
            => fun (xs : List.{u} T)
            => fun (hxs : Eq.{(succ u)} (List.{u} T) (List.append.{u} T xs (List.nil.{u} T)) xs)
            => Eq.cong.{(succ u), (succ u)} (List.{u} T) (List.{u} T)
                (List.append.{u} T xs (List.nil.{u} T))
                xs
                (List.cons.{u} T x)
                hxs)
        l

-- length (l ++ r) = length l + length r
def List.append_length.{u} (T : Type u) (l : List.{u} T) (r : List.{u} T)
        : Eq.{1} Nat (List.length.{u} T (List.append.{u} T l r)) (Nat.add (List.length.{u} T l) (List.length.{u} T r))
    := List.rec.{u, 0} T
        (fun (l : List.{u} T) => Eq.{1} Nat (List.length.{u} T (List.append.{u} T l r)) (Nat.add (List.length.{u} T l) (List.length.{u} T r)))
        (Eq.refl.{1} Nat (List.length.{u} T r))
        (fun (_ : T)
            => fun (xs : List.{u} T)
            => fun (hxs : Eq.{1} Nat (List.length.{u} T (List.append.{u} T xs r)) (Nat.add (List.length.{u} T xs) (List.length.{u} T r)))
            => (Nat.cong (List.length.{u} T (List.append.{u} T xs r)) (Nat.add (List.length.{u} T xs) (List.length.{u} T r)) Nat.succ hxs))
        l

-- map f (l1 ++ l2) = (map f l1) ++ (map f l2)
def List.map_append_equiv.{t, u} (T : Type t) (U : Type u) (f : T -> U) (l1 : List.{t} T) (l2 : List.{t} T)
        : Eq.{(succ u)} (List.{u} U)
            (List.map.{t, u} T U f (List.append.{t} T l1 l2))
            (List.append.{u} U (List.map.{t, u} T U f l1) (List.map.{t, u} T U f l2))
    := List.rec.{t, 0} T
        (fun (l1 : List.{t} T) => Eq.{(succ u)} (List.{u} U)
                                      (List.map.{t, u} T U f (List.append.{t} T l1 l2))
                                      (List.append.{u} U (List.map.{t, u} T U f l1) (List.map.{t, u} T U f l2)))
        (Eq.refl.{(succ u)} (List.{u} U) (List.map.{t, u} T U f l2))
        (fun (x : T)
            => fun (xs : List.{t} T)
            => fun (hxs : Eq.{(succ u)} (List.{u} U)
                          (List.map.{t, u} T U f (List.append.{t} T xs l2))
                          (List.append.{u} U (List.map.{t, u} T U f xs) (List.map.{t, u} T U f l2)))
            => Eq.cong.{(succ u), (succ u)} (List.{u} U) (List.{u} U)
                (List.map.{t, u} T U f (List.append.{t} T xs l2))
                (List.append.{u} U (List.map.{t, u} T U f xs) (List.map.{t, u} T U f l2))
                (List.cons.{u} U (f x))
                hxs)
        l1