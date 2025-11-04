def t1.{u, v} (T : Sort (max (imax u v) (imax v u))) : Sort (max (imax v u) (imax u v)) := T
def t2.{u, v, w} (T : Sort (max (imax u v) (imax u w))) : Sort (max (imax u w) (imax u v)) := T
