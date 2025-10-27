def t1.{u} (T : Sort (imax u 1)) : Sort (max u 1) := T
def t2.{u, v} (T : Sort (imax u (succ v))) : Sort (max u (succ v)) := T
def t3.{u, v} (T : Sort (imax u (max v 1))) : Sort (max (max u v) 1) := T
