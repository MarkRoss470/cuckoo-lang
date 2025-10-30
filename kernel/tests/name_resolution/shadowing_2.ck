data T : Type where
  | c : T

def c : T := T.c

def a (T : Type) (x : T) : T := x -- Good
def a (T : Type) (x : T) : T := c -- Error
