data Unit : Type where
  | mk : Unit

def t1 : Unit -> Unit := fun (u : Unit) => u
def t2 : Unit -> Unit := fun (u : Unit) => Unit.mk
def t3 : Unit -> Unit := fun (_ : Unit) => Unit.mk
