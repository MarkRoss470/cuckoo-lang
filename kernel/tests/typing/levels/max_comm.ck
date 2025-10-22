def d1.{u} (T : Sort (max u 2)) : Sort (max 2 u) := T
def d2.{u, v} (T : Sort (max u v)) : Sort (max v u) := T
def d3.{u, v, w} (T : Sort (max u (max v w))) : Sort (max (max u v) w) := T
def d4.{u, v, w} (T : Sort (max w (max v u))) : Sort (max (max u v) w) := T
def d5.{u, v, w} (T : Sort (max (max v w) u)) : Sort (max (max u v) w) := T
