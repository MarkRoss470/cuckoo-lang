data T : Type where
data U : Type where

def a (f : T -> U) (x : U) : U := f x