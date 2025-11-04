data T.{u} : Type where
  | c : T

def a : T.{1} := T.c.{_}