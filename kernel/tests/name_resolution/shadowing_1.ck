def a (P : Prop) (x : P) (P : Prop) (y : P) : P := y -- Good
def a (P : Prop) (x : P) (P : Prop) (y : P) : P := x -- Error
