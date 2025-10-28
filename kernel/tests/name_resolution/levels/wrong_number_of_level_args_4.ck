data T : Type where
  | c : T

def a : T := T.c.{0}