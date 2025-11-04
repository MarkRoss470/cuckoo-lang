data T : Type where
  | c : T

data Dep (Ty : Type) : Type where
  | mk : Ty -> Dep Ty

def a : Dep T := Dep.mk _ T
