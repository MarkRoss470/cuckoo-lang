data Unit : Type where
  | mk : Unit

data Dep : Unit -> Type where
  | c1 : (u : Unit) -> Dep u
  | c2 : (u : Unit) -> Dep Unit.mk

def t1 : (u : Unit) -> Dep u := fun (u : Unit) => Dep.c1 u
def t2 : (u : Unit) -> Dep Unit.mk := fun (u : Unit) => Dep.c1 Unit.mk
def t3 : (u : Unit) -> Dep Unit.mk := fun (u : Unit) => Dep.c2 u
def t4 : (u : Unit) -> Dep Unit.mk := fun (u : Unit) => Dep.c2 Unit.mk