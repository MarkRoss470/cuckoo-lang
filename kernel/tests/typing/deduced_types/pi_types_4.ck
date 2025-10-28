def T1.{t, u} (T : Sort t) (U : Sort u) : Sort (imax t u) := T -> U
def T2.{t, u, v} (T : Sort t) (U : Sort u) (V : Sort v) : Sort (imax t (imax u v)) := T -> U -> V
