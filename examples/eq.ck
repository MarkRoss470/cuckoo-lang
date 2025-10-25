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