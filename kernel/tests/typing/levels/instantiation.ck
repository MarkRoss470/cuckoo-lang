data T.{u, v} : Sort (max (imax (succ u) v) (max 1 2)) where

def i00 : Sort 2 := T.{0, 0}
def i01 : Sort 2 := T.{0, 1}
def i11 : Sort 2 := T.{1, 1}
def i20 : Sort 2 := T.{2, 0}
def i21 : Sort 3 := T.{2, 1}
def i22 : Sort 3 := T.{2, 2}
def i24 : Sort 4 := T.{2, 4}