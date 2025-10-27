def t1.{u} (T : Sort (max 0 (succ u))) : Sort (succ u) := T -- Good
def t2.{u} (T : Sort (max 1 (succ u))) : Sort (succ u) := T -- Good
def t3.{u} (T : Sort (max 2 (succ u))) : Sort (succ u) := T -- Error
