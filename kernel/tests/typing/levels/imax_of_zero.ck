def t1.{u} (T : Sort (imax u 0)) : Sort 0 := T
def t2.{u, v} (T : Sort (imax u (imax v 0))) : Sort 0 := T
def t3.{u, v} (T : Sort (imax u (max 0 0))) : Sort 0 := T
