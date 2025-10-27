def t1.{u, v, w} (T : Sort (imax u (imax v w))) : Sort (imax v (imax u w)) := T
def t2.{u, v, w} (T : Sort (imax u (imax v w))) : Sort (imax (max u v) w) := T
