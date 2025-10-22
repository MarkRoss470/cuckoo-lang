def d1 (T : Prop) : Sort 0 := T
def d2 (T : Type) : Sort 1 := T
def d3.{u} (T : Type u) : Sort (succ u) := T
