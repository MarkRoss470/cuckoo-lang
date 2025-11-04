data T : Type where
  | c : T

def a : T -> T -> T := fun (x y : T) => x