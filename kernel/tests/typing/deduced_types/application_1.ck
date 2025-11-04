data T1 : Type where
  | c : T1

data T2 : Type where
  | c : T2

def f : T1 -> T2 := fun (_ : T1) => T2.c
def g : T2 := f T1.c