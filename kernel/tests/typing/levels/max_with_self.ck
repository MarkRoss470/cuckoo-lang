def d1.{u} (T : Sort (max u u)) : Sort u := T
def d2.{u, v} (T : Sort (max (max u v) (max u v))) : Sort (max u v) := T
def d3.{u} (T : Sort (max (max u 2) (max u 2))) : Sort (max u 2) := T
def d4.{u, v} (T : Sort (max (max u v) (max v u))) : Sort (max u v) := T
